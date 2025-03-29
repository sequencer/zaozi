// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.magic

import scala.quoted.*
import scala.language.reflectiveCalls
import scala.reflect.Selectable.reflectiveSelectable

/** This macro takes [[fieldName]] from dynamic access, retrieve type at compile time and call runtimeSelectDynamic to
  * do subaccess
  *
  * TODO: think about:
  * {{{
  *   trait RefElementViaValName[D <: Data, R <: Referable[D]]:
  *     extension (ref: R)
  *     def refViaValName[E <: Data](
  *       fieldName: String,
  *       ctx:       Context,
  *       file:      sourcecode.File,
  *       line:      sourcecode.Line,
  *       valName:   sourcecode.Name
  *     ): Ref[E]
  *   given [D <: Bundle, R <: Referable[D]]: RefElementViaValName[D, R]
  * }}}
  * macro here can use Implicits.search to find the implicit instance from given. another issue is I don't have a good
  * idea to deal with valName on BundleField.
  */
def referableSelectDynamic[T <: me.jiuyang.zaozi.valuetpe.Data: Type](
  ref:       Expr[me.jiuyang.zaozi.reftpe.Referable[T]],
  fieldName: Expr[String]
)(
  using Quotes
): Expr[Any] =
  import quotes.reflect.*

  // Get the type of `tpe` field from `Referable`
  val referableType       = TypeRepr.of[T]
  val dynamicSubfieldType = TypeRepr.of[me.jiuyang.zaozi.magic.DynamicSubfield]

  // Ensure T is a subtype of Bundle
  if (!(referableType <:< dynamicSubfieldType)) {
    report.errorAndAbort(s"Type parameter T must be a subtype of DynamicSubfield, but got ${referableType.show}.")
  }

  // Check if the field exists in the Bundle type
  val fieldNameStr   = fieldName.valueOrAbort
  val fieldSymbolOpt = referableType.classSymbol.flatMap(_.declaredFields.find(_.name == fieldNameStr))
  val fieldSymbol    = fieldSymbolOpt.getOrElse {
    report.errorAndAbort(s"Field '$fieldNameStr' does not exist in type ${referableType.show}.")
  }

  val fieldType = fieldSymbol.tree match {
    case ValDef(_, fieldTypeRepr, _) =>
      // Find the Path-dependent type:
      if (
        fieldTypeRepr.tpe.typeArgs.headOption.map(_.typeSymbol.maybeOwner == referableType.typeSymbol).getOrElse(false)
      )
        val dataTypeRepr = fieldTypeRepr.tpe.typeArgs.head
        // Maintain a map to recovery this.T to concrete type from parameters.
        val localTypes   = referableType.classSymbol.get.declaredTypes
        val typeArgs     = referableType.typeArgs
        // substitute from local type to parameters
        fieldTypeRepr.tpe.substituteTypes(from = localTypes, to = typeArgs)
      else fieldTypeRepr.tpe
    case _                           => report.errorAndAbort(s"Unable to determine the type of field '$fieldNameStr'.")
  }

  // Ensure the field type conforms to Data
  val bundleFieldType = TypeRepr.of[me.jiuyang.zaozi.valuetpe.BundleField[?]]
  if (!(fieldType <:< bundleFieldType)) {
    report.errorAndAbort(s"Field type '${fieldType.show}' does not conform to the upper bound BundleField.")
  }

  // Summon implicit parameters
  val arena = Expr.summon[java.lang.foreign.Arena].getOrElse {
    report.errorAndAbort("No implicit value found for Arena.")
  }

  val typeImpl = Expr.summon[me.jiuyang.zaozi.TypeImpl].getOrElse {
    report.errorAndAbort("No implicit value found for Arena.")
  }

  val context = Expr.summon[org.llvm.mlir.scalalib.Context].getOrElse {
    report.errorAndAbort("No implicit value found for Context.")
  }

  val block = Expr.summon[org.llvm.mlir.scalalib.Block].getOrElse {
    report.errorAndAbort("No implicit value found for Block.")
  }

  val file = Expr.summon[sourcecode.File].getOrElse {
    report.errorAndAbort("No implicit value found for sourcecode.File.")
  }

  val line = Expr.summon[sourcecode.Line].getOrElse {
    report.errorAndAbort("No implicit value found for sourcecode.Line.")
  }

  val valName = Expr.summon[sourcecode.Name].getOrElse {
    report.errorAndAbort("No implicit value found for sourcecode.Name.")
  }

  val fieldDataType = fieldType.typeArgs.head

  // Construct and return the expression ref.field(fieldName)
  fieldDataType.asType match {
    case tpe @ '[fieldDataType] =>
      '{
        given java.lang.foreign.Arena        = $arena
        given me.jiuyang.zaozi.TypeImpl      = $typeImpl
        given org.llvm.mlir.scalalib.Context = $context
        given org.llvm.mlir.scalalib.Block   = $block
        given sourcecode.File                = $file
        given sourcecode.Line                = $line
        given sourcecode.Name                = $valName
        $ref._tpe
          .asInstanceOf[me.jiuyang.zaozi.magic.DynamicSubfield]
          // Hack with union type
          .getRefViaFieldValName[fieldDataType & me.jiuyang.zaozi.valuetpe.Data](
            $ref.refer,
            $fieldName
          )
      }
    case _                      =>
      report.errorAndAbort(s"Field type '${fieldType.show}' does not conform to the upper bound Data.")
  }

def referableApplyDynamic[T <: me.jiuyang.zaozi.valuetpe.Data: Type](
  ref:       Expr[me.jiuyang.zaozi.reftpe.Referable[T]],
  fieldName: Expr[String],
  args:      Expr[Seq[Any]]
)(
  using Quotes
): Expr[Any] =
  import quotes.reflect.*
  // Get the "field" expression via selectDynamic
  val fieldValueExpr: Expr[Any] = referableSelectDynamic[T](ref, fieldName)

  // Deconstruct the varargs
  // TODO: How to fix: varargs is not capture at compileTime!
  //       [error] -- Error: zaozi/zaozi/tests/src/VecSpec.scala:43:18 ---
  //       [error] 43 |        io.out := io.a(io.idx)
  //       [error]    |                  ^^^^^^^^^^^
  //       [error]    |                  Expected varargs for applyDynamic, got: args$proxy1
  val varargs = args match
    case Varargs(exprs) => exprs
    case other          =>
      report.errorAndAbort(s"Expected varargs for applyDynamic, got: ${other.show}")

  // Build an Apply node: fieldValue.apply(arg1, arg2, ...)
  val fieldValueTerm = fieldValueExpr.asTerm
  val applyCallTerm  =
    Apply(
      Select.unique(fieldValueTerm, "apply"), // fieldValue.apply
      varargs.map(_.asTerm).toList
    )

  // Turn it back into an Expr
  applyCallTerm.asExpr

def referableApplyDynamicNamed[T <: me.jiuyang.zaozi.valuetpe.Data: Type](
  ref:       Expr[me.jiuyang.zaozi.reftpe.Referable[T]],
  fieldName: Expr[String],
  args:      Expr[Seq[(String, Any)]]
)(
  using Quotes
): Expr[Any] =
  import quotes.reflect.*

  // Get the "field" expression via selectDynamic
  val fieldValueExpr: Expr[Any] = referableSelectDynamic[T](ref, fieldName)

  // Deconstruct the varargs
  val varargs: Seq[(String, Expr[Any])] = args match
    case Varargs(argExprs) =>
      argExprs.map {
        case '{ ($key: String, $value: Any) } =>
          key.value match
            case Some(k) => (k, value)
            case None    =>
              report.errorAndAbort("Named argument must have a statically known key string.")
        case other                            =>
          report.errorAndAbort(s"Expected a literal (String, Any), got: ${other.show}")
      }
    case other             =>
      report.errorAndAbort(s"Expected varargs for applyDynamicNamed, got: ${other.show}")

  // Build a call with NamedArg nodes for each parameter
  val fieldValueTerm = fieldValueExpr.asTerm
  val namedArgs      = varargs.map { case (k, v) =>
    NamedArg(k, v.asTerm)
  }

  // Turn it back into an Expr
  val applyCallTerm =
    Apply(
      Select.unique(fieldValueTerm, "apply"), // fieldValue.apply
      namedArgs.toList
    )

  // Turn it back into an Expr
  applyCallTerm.asExpr
