// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Yuhang Zeng <unlsycn@unlsycn.com>
package me.jiuyang.zaozi.magic.macros

import scala.annotation.{experimental, MacroAnnotation}
import scala.quoted.*

@experimental
class generator extends MacroAnnotation:
  def transform(
    using Quotes
  )(definition: quotes.reflect.Definition,
    companion:  Option[quotes.reflect.Definition]
  ): List[quotes.reflect.Definition] =
    import quotes.reflect.*
    definition match
      case ClassDef(name, constr, parents, selfOpt, body)
          // a bit of dirty but quotes does not expose the SingletonTypeTree
          if selfOpt.exists(_.tpt.toString().startsWith("SingletonTypeTree")) =>
        val objSym                    = definition.symbol
        val (typeParam, typeI, typeP) = parents
          .map(parent =>
            parent match
              case Applied(generatorName, List(param: TypeIdent, i: TypeIdent, p: TypeIdent)) =>
                Some(param, i, p)
              case _                                                                          => None
          )
          .flatten
          .headOption
          .getOrElse {
            report.errorAndAbort("@generator object should extends trait Generator")
          }

        def makeInterfaceDef(symbolName: String, resultType: TypeTree) = DefDef(
          Symbol.newMethod(
            objSym,
            symbolName,
            // we have to construct MethodType manually since the type is different with the declaration's in Generator
            MethodType(List("parameter"))(methodType => List(typeParam.tpe), methodType => resultType.tpe)
          ),
          (argss: List[List[Tree]]) =>
            Some(Select.unique(New(resultType), "<init>").appliedTo(argss.head.head.asExpr.asTerm))
        )

        val interfaceDef = makeInterfaceDef("interface", typeI)
        val probeDef     = makeInterfaceDef("probe", typeP)

        def generatorApiCall(implName: String) = (argss: List[List[Tree]]) =>
          Some(
            argss match
              case List(argList, contextualArgList) =>
                Select
                  .unique(Ref(Symbol.requiredModule("me.jiuyang.zaozi.default.given_GeneratorApi")), implName)
                  .appliedToTypeTrees(List(typeParam, typeI, typeP))
                  .appliedTo(This(objSym))
                  .appliedToArgs(argList.map(_.asExpr.asTerm))
                  .appliedToArgs(contextualArgList.map(_.asExpr.asTerm))
              case _                                => report.errorAndAbort("should not reach here")
          )

        val moduleDef = DefDef(
          Symbol.newMethod(
            objSym,
            "module",
            // only the first parameter list has generic type so we concretize it based on the original type
            // note that requiredMethod cannot get the parameter types
            Symbol.requiredClass("me.jiuyang.zaozi.Generator").declarations.find(_.name == "module").get.info match
              case MethodType(paramList, _, resultType) =>
                MethodType(paramList)(methodType => List(typeParam.tpe), methodType => resultType)
          ),
          generatorApiCall("moduleImpl")
        )

        val instanceDef = DefDef(
          Symbol.newMethod(
            objSym,
            "instance",
            Symbol.requiredClass("me.jiuyang.zaozi.Generator").declarations.find(_.name == "instance").get.info match
              case MethodType(
                    paramList,
                    _,
                    MethodType(paramList2, contextualParamList, AppliedType(instanceType, _))
                  ) =>
                MethodType(paramList)(
                  methodType => List(typeParam.tpe),
                  methodType =>
                    MethodType(MethodTypeKind.Contextual)(paramList2)(
                      methodType => contextualParamList,
                      methodType => AppliedType(instanceType, List(typeI, typeP).map(_.tpe))
                    )
                )
          ),
          generatorApiCall("instanceImpl")
        )

        val newBody = interfaceDef :: probeDef :: moduleDef :: instanceDef :: body
        List(ClassDef.copy(definition)(name, constr, parents, selfOpt, newBody))
      case _ =>
        report.error("@generator should only annotate an object")
        List(definition)
