// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Yuhang Zeng <unlsycn@unlsycn.com>
package me.jiuyang.zaozi.magic.macros

import scala.annotation.{experimental, MacroAnnotation}
import scala.quoted.*
import scala.util.chaining.*

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
        val objSym                 = definition.symbol
        val (tpiParam, tpiI, tpiP) = parents
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
            MethodType(List("parameter"))(methodType => List(tpiParam.tpe), methodType => resultType.tpe)
          ),
          (argss: List[List[Tree]]) =>
            Some(Select.unique(New(resultType), "<init>").appliedTo(argss.head.head.asExpr.asTerm))
        )

        def makeParseParameterDef =
          val tpsParam = tpiParam.tpe.typeSymbol
          Seq(selfOpt.get.tpt, tpiParam, tpsParam.companionModule.tree.asInstanceOf[ValDef].tpt)
            .map(_.tpe.asType) match
            case Seq('[tObj], '[tParam], '[tCompanion]) =>
              def parseParameterImpl(
                args:        Expr[Seq[String]]
              )(
                using owner: Quotes
              ) =
                // Ref: https://github.com/com-lihaoyi/mainargs/blob/e815520df9762111643208d57898441d87105811/mainargs/src-3/Macros.scala#L41
                val paramConstructor = tpsParam.companionModule
                  .memberMethod("apply")
                  .filter(p =>
                    p.paramSymss.flatten.corresponds(tpsParam.primaryConstructor.paramSymss.flatten): (p1, p2) =>
                      p1.name == p2.name
                  )
                  .headOption
                  .getOrElse {
                    report.errorAndAbort(
                      s"Cannot find apply method in companion object of ${tpiParam.tpe.show}",
                      tpsParam.companionModule.pos.getOrElse(Position.ofMacroExpansion)
                    )
                  }
                val argSigs          = Expr.ofList(
                  tpiParam.symbol.declaredFields
                    .map: param =>
                      param.tree.asInstanceOf[ValDef].tpt.tpe.asType match
                        case '[t] =>
                          val tokensReader = Expr
                            .summon[mainargs.TokensReader[t]]
                            .getOrElse:
                              report.errorAndAbort(
                                s"No TokensReader[${Type.show[t]}] found for parameter ${param.name}"
                              )

                          '{
                            mainargs.ArgSig
                              .create[t, tObj](
                                ${ Expr(param.name) },
                                new mainargs.arg,
                                None // TODO: support default value
                              )(
                                using ${ tokensReader }
                              )
                          }
                )
                val invokeRaw        =
                  def callOf(
                    methodOwner: Expr[Any],
                    args:        Expr[Seq[Any]]
                  )(
                    using Quotes
                  ) =
                    val params = paramConstructor.paramSymss.head
                    methodOwner.asTerm
                      .select(paramConstructor)
                      .appliedToArgs(params.map: param =>
                        methodOwner.asTerm.tpe.memberType(paramConstructor).memberType(param).asType match
                          case '[t] => '{ $args(${ Expr(params.indexOf(param)) }).asInstanceOf[t] }.asTerm
                      )
                      .asExprOf[tParam]

                  '{ (b: tCompanion, params: Seq[Any]) => ${ callOf('b, 'params) } }

                val mainData = '{
                  mainargs.MainData
                    .create[tParam, tCompanion](
                      "apply",
                      new mainargs.main,
                      ${ argSigs },
                      ${ invokeRaw }
                    )
                }
                '{
                  (new mainargs.ParserForClass[tParam](
                    $mainData.asInstanceOf[mainargs.MainData[tParam, Any]],
                    () =>
                      ${
                        Ident(tpiParam.tpe match
                          case TypeRef(a, b) => TermRef(a, b)
                        ).asExpr
                      }
                  )).constructOrExit(${ args })
                }

              val parseParameterSymbol = Symbol.newMethod(
                objSym,
                "parseParameter",
                MethodType(List("args"))(
                  methodType => List(TypeRepr.of[Seq[String]]),
                  methodType => TypeRepr.of[tParam]
                )
              )
              DefDef(
                parseParameterSymbol,
                (argss: List[List[Tree]]) =>
                  Some(
                    parseParameterImpl(argss.head.head.asExprOf[Seq[String]])(
                      // pass method symbol as owner
                      using parseParameterSymbol.asQuotes
                    ).asTerm
                  )
              )

        def makeMainDef = DefDef(
          Symbol.newMethod(
            objSym,
            "main",
            Symbol.requiredClass("me.jiuyang.zaozi.Generator").declaredMethod("main").head.info
          ),
          (argss: List[List[Tree]]) =>
            tpiParam.tpe.asType match
              case '[tParam] =>
                Some(
                  Select
                    .unique(Ref(Symbol.requiredModule("me.jiuyang.zaozi.default.given_GeneratorApi")), "mainImpl")
                    .appliedToTypeTrees(List(tpiParam, tpiI, tpiP))
                    .appliedTo(This(objSym))
                    .appliedTo(argss.head.head.asExpr.asTerm)
                    .appliedTo(
                      Expr
                        .summon[upickle.default.ReadWriter[tParam]]
                        .getOrElse:
                          report.errorAndAbort(
                            s"No given instance of upickle.default.ReadWriter[${tpiParam.show}] was Found"
                          )
                        .asTerm
                    )
                )
        )

        def defOpt[D <: Definition](definition: D) =
          Option.unless(definition.symbol.overridingSymbol(objSym).exists)(definition)

        val interfaceDefOpt = makeInterfaceDef("interface", tpiI).pipe(defOpt)
        val probeDefOpt     = makeInterfaceDef("probe", tpiP).pipe(defOpt)

        val parseParameterDefOpt = makeParseParameterDef.pipe(defOpt)
        val mainDefOpt           = makeMainDef.pipe(defOpt)

        val newBody = List(interfaceDefOpt, probeDefOpt, parseParameterDefOpt, mainDefOpt).flatten ++ body
        List(ClassDef.copy(definition)(name, constr, parents, selfOpt, newBody))
      case _ =>
        report.error("@generator should only annotate an object")
        List(definition)
