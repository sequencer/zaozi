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

        val newBody = interfaceDef :: probeDef :: body
        List(ClassDef.copy(definition)(name, constr, parents, selfOpt, newBody))
      case _ =>
        report.error("@generator should only annotate an object")
        List(definition)
