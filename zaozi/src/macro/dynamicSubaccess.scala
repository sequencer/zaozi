package me.jiuyang.zaozi

import scala.quoted.*

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
  * macro here can use Implicits.search to find the implicit instance from given.
  * another issue is I don't have a good idea to deal with valName on BundleField.
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

  val fieldType = fieldSymbol.tree match {
    case ValDef(_, fieldTypeRepr, _) =>
      // Find the Path-dependent type:
      if(fieldTypeRepr.tpe.typeArgs.headOption.map(_.typeSymbol.maybeOwner == referableType.typeSymbol).getOrElse(false))
        val dataTypeRepr = fieldTypeRepr.tpe.typeArgs.head
        // Maintain a map to recovery this.T to concrete type from parameters.
        val localTypes = referableType.classSymbol.get.declaredTypes
        val typeArgs = referableType.typeArgs
        // substitute from local type to parameters
        fieldTypeRepr.tpe.substituteTypes(from = localTypes, to = typeArgs)
      else
        fieldTypeRepr.tpe
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
