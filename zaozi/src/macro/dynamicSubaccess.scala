package me.jiuyang.zaozi

import scala.quoted.*

def dynamicSubaccess[T <: Data: Type](
  ref:       Expr[Referable[T]],
  fieldName: Expr[String]
)(
  using Quotes
): Expr[Any] =
  import quotes.reflect.*

  // Get the type of `tpe` field from `Referable`
  val referableType = TypeRepr.of[T]
  val bundleType    = TypeRepr.of[Bundle]

  // Ensure T is a subtype of Bundle
  if (!(referableType <:< bundleType)) {
    report.errorAndAbort(s"Type parameter T must be a subtype of Bundle, but got ${referableType.show}.")
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
  val dataType = TypeRepr.of[Data]
  if (!(fieldType <:< dataType)) {
    report.errorAndAbort(s"Field type '${fieldType.show}' does not conform to the upper bound Data.")
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

  // Construct and return the expression ref.field(fieldName)
  fieldType.asType match {
    case tpe @ '[fieldType] if TypeRepr.of[fieldType] <:< TypeRepr.of[Data] =>
      '{
        // Hack with union type
        $ref._field[fieldType & Data]($fieldName)(
          using $ctx,
          $file,
          $line,
          $valName
        )
      }
    case _                                                                  =>
      report.errorAndAbort(s"Field type '${fieldType.show}' does not conform to the upper bound Data.")
  }
