// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.magic

import scala.language.reflectiveCalls
import scala.quoted.*
import scala.reflect.Selectable.reflectiveSelectable

private def summonImplicitParameters(
  using Quotes
) =
  import quotes.reflect.*
  val arena    = Expr.summon[java.lang.foreign.Arena].getOrElse {
    report.errorAndAbort("No implicit value found for Arena.")
  }
  val typeImpl = Expr.summon[me.jiuyang.zaozi.TypeImpl].getOrElse {
    report.errorAndAbort("No implicit value found for Arena.")
  }
  val context  = Expr.summon[org.llvm.mlir.scalalib.Context].getOrElse {
    report.errorAndAbort("No implicit value found for Context.")
  }
  val block    = Expr.summon[org.llvm.mlir.scalalib.Block].getOrElse {
    report.errorAndAbort("No implicit value found for Block.")
  }
  val file     = Expr.summon[sourcecode.File].getOrElse {
    report.errorAndAbort("No implicit value found for sourcecode.File.")
  }
  val line     = Expr.summon[sourcecode.Line].getOrElse {
    report.errorAndAbort("No implicit value found for sourcecode.Line.")
  }
  val valName  = Expr.summon[sourcecode.Name.Machine].getOrElse {
    report.errorAndAbort("No implicit value found for sourcecode.Name.Machine.")
  }

  (arena, typeImpl, context, block, file, line, valName)

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
  *       valName:   sourcecode.Name.Machine
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

  val (arena, typeImpl, context, block, file, line, valName) = summonImplicitParameters

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
        given sourcecode.Name.Machine        = $valName
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

object ApplyHelper:
  import me.jiuyang.zaozi.valuetpe.*
  import me.jiuyang.zaozi.reftpe.*
  import org.llvm.mlir.scalalib.*
  import java.lang.foreign.Arena

  def vecApplyWrapper[E <: Data, V <: Vec[E], R <: Referable[V]](
    vecRef: R,
    idx:    Referable[UInt] | Int
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name.Machine
  ): Node[E] =
    import me.jiuyang.zaozi.default.given_VecApi_E_V_R
    vecRef.apply(idx)

  def bitsApplyBitsWrapper[R <: Referable[Bits]](
    bitsRef: R,
    hi:      Int,
    lo:      Int
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name.Machine
  ): Node[Bits] =
    import me.jiuyang.zaozi.default.given_BitsApi_R
    bitsRef.apply(hi, lo)

  def bitsApplyBitWrapper[R <: Referable[Bits]](
    bitsRef: R,
    idx:     Int
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name.Machine
  ): Node[Bits] =
    import me.jiuyang.zaozi.default.given_BitsApi_R
    bitsRef.apply(idx)

private def getTypeParameters(
  fieldValueExpr: Expr[Any]
)(
  using Quotes
) =
  import quotes.reflect.*

  val rType                = fieldValueExpr.asTerm.tpe
  if (!(rType <:< TypeRepr.of[me.jiuyang.zaozi.reftpe.Referable[?]]))
    report.errorAndAbort(s"Type parameter R must be a subtype of Referable, but got ${rType.show}.")
  val (vTypeOpt, eTypeOpt) = rType.match
    case AppliedType(_, List(vecAndData)) =>
      vecAndData match
        case AndType(vecOrBits, _) =>
          vecOrBits match
            case AppliedType(_, List(data)) =>
              if (!(vecOrBits <:< TypeRepr.of[me.jiuyang.zaozi.valuetpe.Vec[?]]))
                report.errorAndAbort(s"Type parameter V must be a subtype of Vec, but got ${vecOrBits.show}.")
              if (!(data <:< TypeRepr.of[me.jiuyang.zaozi.valuetpe.Data]))
                report.errorAndAbort(s"Type parameter E must be a subtype of Data, but got ${data.show}.")
              (Some(vecOrBits), Some(data))
            case bits                       =>
              if (!(bits =:= TypeRepr.of[me.jiuyang.zaozi.valuetpe.Bits]))
                report.errorAndAbort(s"Element type must be Bits, but got ${bits.show}.")
              (None, None)

  (rType, vTypeOpt, eTypeOpt)

def referableApplyDynamic[T <: me.jiuyang.zaozi.valuetpe.Data: Type](
  ref:       Expr[me.jiuyang.zaozi.reftpe.Referable[T]],
  fieldName: Expr[String],
  args:      Expr[Seq[Any]]
)(
  using Quotes
): Expr[Any] =
  import quotes.reflect.*
  // Get the "field" expression via selectDynamic
  val fieldValueExpr = referableSelectDynamic[T](ref, fieldName)

  // Deconstruct the varargs
  val varargs = args match
    case Varargs(exprs) => exprs
    case other          =>
      report.errorAndAbort(s"Expected varargs for applyDynamic, got: ${other.show}")

  val (arena, _, context, block, file, line, valName) = summonImplicitParameters

  // If we have more than one apply() method, we can dispatch them here based on the args type.
  val applyCallTerm = getTypeParameters(fieldValueExpr) match
    case (rType, Some(vType), Some(eType)) =>
      varargs match
        case idx +: Nil =>
          Select
            .unique(
              Ref(Symbol.requiredModule("me.jiuyang.zaozi.magic.ApplyHelper")),
              "vecApplyWrapper"
            )
            .appliedToTypes(List(eType, vType, rType))
            .appliedToArgs(List(fieldValueExpr, idx).map(_.asTerm))
            .appliedToArgs(List(arena, context, block, file, line, valName).map(_.asTerm))
        case _          => report.errorAndAbort(s"Expected 1 args, but got ${varargs.length}")
    case (rType, None, None)               =>
      varargs match
        case idx +: Nil      =>
          Select
            .unique(
              Ref(Symbol.requiredModule("me.jiuyang.zaozi.magic.ApplyHelper")),
              "bitsApplyBitWrapper"
            )
            .appliedToTypes(List(rType))
            .appliedToArgs(List(fieldValueExpr, idx).map(_.asTerm))
            .appliedToArgs(List(arena, context, block, file, line, valName).map(_.asTerm))
        case hi +: lo +: Nil =>
          Select
            .unique(
              Ref(Symbol.requiredModule("me.jiuyang.zaozi.magic.ApplyHelper")),
              "bitsApplyBitsWrapper"
            )
            .appliedToTypes(List(rType))
            .appliedToArgs(List(fieldValueExpr, hi, lo).map(_.asTerm))
            .appliedToArgs(List(arena, context, block, file, line, valName).map(_.asTerm))
        case _               => report.errorAndAbort(s"Expected 1 or 2 args, but got ${varargs.length}")
    case (rType, vTypeOpt, eTypeOpt)       =>
      report.errorAndAbort(
        s"Unexpected type parameters ${rType.show}, ${vTypeOpt.flatMap(t => Some(t.show))} and ${eTypeOpt
            .flatMap(t => Some(t.show))}"
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
  val fieldValueExpr = referableSelectDynamic[T](ref, fieldName)

  // Deconstruct the varargs
  val varargs = args match
    case Varargs(argExprs) =>
      argExprs.map {
        case '{ ($key: String, $value: Any) } =>
          key.value match
            case Some(k) => NamedArg(k, value.asTerm)
            case None    =>
              report.errorAndAbort("Named argument must have a statically known key string.")
        case other                            =>
          report.errorAndAbort(s"Expected a literal (String, Any), got: ${other.show}")
      }
    case other             =>
      report.errorAndAbort(s"Expected varargs for applyDynamicNamed, got: ${other.show}")

  val (arena, _, context, block, file, line, valName) = summonImplicitParameters

  val applyCallTerm = getTypeParameters(fieldValueExpr) match
    case (rType, Some(vType), Some(eType)) =>
      varargs match
        case idx +: Nil =>
          Select
            .unique(
              Ref(Symbol.requiredModule("me.jiuyang.zaozi.magic.ApplyHelper")),
              "vecApplyWrapper"
            )
            .appliedToTypes(List(eType, vType, rType))
            .appliedToArgs(List(fieldValueExpr.asTerm, idx))
            .appliedToArgs(List(arena, context, block, file, line, valName).map(_.asTerm))
        case _          => report.errorAndAbort(s"Expected 1 args, but got ${varargs.length}")
    case (rType, None, None)               =>
      varargs match
        case idx +: Nil      =>
          Select
            .unique(
              Ref(Symbol.requiredModule("me.jiuyang.zaozi.magic.ApplyHelper")),
              "bitsApplyBitWrapper"
            )
            .appliedToTypes(List(rType))
            .appliedToArgs(List(fieldValueExpr.asTerm, idx))
            .appliedToArgs(List(arena, context, block, file, line, valName).map(_.asTerm))
        case hi +: lo +: Nil =>
          Select
            .unique(
              Ref(Symbol.requiredModule("me.jiuyang.zaozi.magic.ApplyHelper")),
              "bitsApplyBitsWrapper"
            )
            .appliedToTypes(List(rType))
            .appliedToArgs(List(fieldValueExpr.asTerm, hi, lo))
            .appliedToArgs(List(arena, context, block, file, line, valName).map(_.asTerm))
        case _               => report.errorAndAbort(s"Expected 1 or 2 args, but got ${varargs.length}")
    case (rType, vTypeOpt, eTypeOpt)       =>
      report.errorAndAbort(
        s"Unexpected type parameters ${rType.show}, ${vTypeOpt.flatMap(t => Some(t.show))} and ${eTypeOpt
            .flatMap(t => Some(t.show))}"
      )

  // Turn it back into an Expr
  applyCallTerm.asExpr
