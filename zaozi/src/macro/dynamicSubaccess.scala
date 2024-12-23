package me.jiuyang.zaozi

import scala.quoted.*

/** This macro takes [[fieldName]] from dynamic access, retrieve type at compile time and call runtimeSelectDynamic to
  * do subaccess
  */
def refSubAccess[T <: Data: Type](
  ref:       Expr[Referable[T]],
  fieldName: Expr[String]
)(
  using Quotes
): Expr[Any] =
  import quotes.reflect.*

  // Get the type of `tpe` field from `Referable`
  val referableType       = TypeRepr.of[T]
  val dynamicSubfieldType = TypeRepr.of[DynamicSubfield]

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

  // Get the type of the field
  val fieldType = fieldSymbol.tree match {
    case ValDef(_, tpt, _) => tpt.tpe
    case _                 => report.errorAndAbort(s"Unable to determine the type of field '$fieldNameStr'.")
  }

  // Ensure the field type conforms to Data
  val bundleFieldType = TypeRepr.of[BundleField[?]]
  if (!(fieldType <:< bundleFieldType)) {
    report.errorAndAbort(s"Field type '${fieldType.show}' does not conform to the upper bound BundleField.")
  }

  // Summon implicit parameters
  val ctx = Expr.summon[me.jiuyang.zaozi.internal.Context].getOrElse {
    report.errorAndAbort("No implicit value found for Context.")
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
        $ref.tpe
          .asInstanceOf[DynamicSubfield]
          // Hack with union type
          .getRefViaFieldValName[fieldDataType & Data]($ref.refer, $fieldName, $ctx, $file, $line, $valName)
      }
    case _                      =>
      report.errorAndAbort(s"Field type '${fieldType.show}' does not conform to the upper bound Data.")
  }

def refSubIdx[T <: Data: Type, IDX: Type](
  ref: Expr[Referable[T]],
  idx: Expr[IDX]
)(
  using Quotes
): Expr[Any] =
  import quotes.reflect.*

  // Summon implicit parameters
  val ctx = Expr.summon[me.jiuyang.zaozi.internal.Context].getOrElse {
    report.errorAndAbort("No implicit value found for Context.")
  }

  val file = Expr.summon[sourcecode.File].getOrElse {
    report.errorAndAbort("No implicit value found for sourcecode.File.")
  }

  val line = Expr.summon[sourcecode.Line].getOrElse {
    report.errorAndAbort("No implicit value found for sourcecode.Line.")
  }

  val valName    = Expr.summon[sourcecode.Name].getOrElse {
    report.errorAndAbort("No implicit value found for sourcecode.Name.")
  }
  // Get the type of `tpe` field from `Referable`
  val tTypeRepr  = TypeRepr.of[T]
  val subIdxSym  = TypeRepr.of[SubIdx[?, IDX]].typeSymbol
  val subIdxBase = tTypeRepr.baseType(subIdxSym)

  subIdxBase match {
    case AppliedType(_, List(ele, _)) =>
      ele.asType match
        case '[elementType] =>
          '{
            $ref.tpe
              .asInstanceOf[SubIdx[elementType & Data, IDX]]
              .getRefViaIdx($ref.refer, $idx, $ctx, $file, $line, $valName)
          }
    case _                            =>
      report.errorAndAbort(s"Type ${tTypeRepr.show} does not extend SubIdx[T] as expected.")
  }
