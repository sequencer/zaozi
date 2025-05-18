// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Yuhang Zeng <unlsycn@unlsycn.com>
package org.llvm.circt.scalalib.om.capi

import org.llvm.circt.*
import org.llvm.circt.CAPI.*
import org.llvm.mlir.scalalib.given
import org.llvm.mlir.scalalib.{Attribute, Context, Identifier, Location, Module, Type, TypeID}

import java.lang.foreign.{Arena, MemorySegment}

given TypeApi with
  extension (tpe: Type)
    inline def isAnyType:            Boolean = omTypeIsAAnyType(tpe.segment)
    inline def isClassType:          Boolean = omTypeIsAClassType(tpe.segment)
    inline def isFrozenBasePathType: Boolean = omTypeIsAFrozenBasePathType(tpe.segment)
    inline def isFrozenPathType:     Boolean = omTypeIsAFrozenPathType(tpe.segment)
    inline def isListType:           Boolean = omTypeIsAListType(tpe.segment)
    inline def isMapType:            Boolean = omTypeIsAMapType(tpe.segment)
    inline def isStringType:         Boolean = omTypeIsAStringType(tpe.segment)
    inline def classTypeGetName(
      using arena: Arena
    ): Identifier = Identifier(omClassTypeGetName(arena, tpe.segment))
    inline def listTypeGetElementType(
      using arena: Arena
    ): Type = Type(omListTypeGetElementType(arena, tpe.segment))
    inline def mapTypeGetKeyType(
      using arena: Arena
    ): Type = Type(omMapTypeGetKeyType(arena, tpe.segment))

  inline def anyTypeGetTypeID(
    using arena: Arena
  ): TypeID = TypeID(omAnyTypeGetTypeID(arena))
  inline def classTypeGetTypeID(
    using arena: Arena
  ): TypeID = TypeID(omClassTypeGetTypeID(arena))
  inline def frozenBasePathTypeGetTypeID(
    using arena: Arena
  ): TypeID = TypeID(omFrozenBasePathTypeGetTypeID(arena))
  inline def frozenPathTypeGetTypeID(
    using arena: Arena
  ): TypeID = TypeID(omFrozenPathTypeGetTypeID(arena))
  inline def listTypeGetTypeID(
    using arena: Arena
  ): TypeID = TypeID(omListTypeGetTypeID(arena))
end given

given EvaluatorApi with
  inline def evaluatorNew(
    module:      Module
  )(
    using arena: Arena
  ): Evaluator = Evaluator(omEvaluatorNew(arena, module.segment))

  extension (evaluator: Evaluator)
    inline def instantiate(
      className:    Attribute,
      actualParams: EvaluatorValue*
    )(
      using arena:  Arena
    ): EvaluatorValue =
      EvaluatorValue(
        omEvaluatorInstantiate(
          arena,
          evaluator.segment,
          className.segment,
          actualParams.length,
          actualParams.toMlirArray
        )
      )

    inline def instantiate(
      className:    String,
      actualParams: EvaluatorValue*
    )(
      using arena:  Arena,
      context:      Context
    ): EvaluatorValue = instantiate(className.stringAttrGet, actualParams*)

    inline def getModule(
      using arena: Arena
    ): Module = new Module(omEvaluatorGetModule(arena, evaluator.segment))

    inline def segment: MemorySegment = evaluator._segment
end given

given ObjectApi with
  extension (omObject: EvaluatorValue)
    inline def objectIsNull: Boolean = omEvaluatorObjectIsNull(omObject.segment)

    inline def objectGetType(
      using arena: Arena
    ): Type = new Type(omEvaluatorObjectGetType(arena, omObject.segment))

    inline def objectGetField(
      name:        Attribute
    )(
      using arena: Arena
    ): EvaluatorValue =
      EvaluatorValue(
        omEvaluatorObjectGetField(
          arena,
          omObject.segment,
          name.segment
        )
      )

    inline def objectGetField(
      name:        String
    )(
      using arena: Arena,
      context:     Context
    ): EvaluatorValue = objectGetField(name.stringAttrGet)

    inline def objectGetHash: Int = omEvaluatorObjectGetHash(omObject.segment).toInt

    inline def objectIsEq(other: EvaluatorValue): Boolean =
      omEvaluatorObjectIsEq(omObject.segment, other.segment)

    inline def objectGetFieldNames(
      using arena: Arena
    ): Attribute = new Attribute(omEvaluatorObjectGetFieldNames(arena, omObject.segment))
end given

given EvaluatorValueApi with
  extension (evaluatorValue: EvaluatorValue)
    inline def getContext(
      using arena: Arena
    ): Context = Context(omEvaluatorValueGetContext(arena, evaluatorValue.segment))

    inline def getLoc(
      using arena: Arena
    ): Location = Location(omEvaluatorValueGetLoc(arena, evaluatorValue.segment))

    inline def isNull: Boolean = omEvaluatorValueIsNull(evaluatorValue.segment)

    inline def isObject: Boolean = omEvaluatorValueIsAObject(evaluatorValue.segment)

    inline def isPrimitive: Boolean = omEvaluatorValueIsAPrimitive(evaluatorValue.segment)

    inline def getPrimitive(
      using arena: Arena
    ): Attribute = Attribute(omEvaluatorValueGetPrimitive(arena, evaluatorValue.segment))

    inline def isList: Boolean = omEvaluatorValueIsAList(evaluatorValue.segment)

    inline def listGetNumElements: Int = omEvaluatorListGetNumElements(evaluatorValue.segment).toInt

    inline def listGetElement(
      pos:         Int
    )(
      using arena: Arena
    ): EvaluatorValue = EvaluatorValue(omEvaluatorListGetElement(arena, evaluatorValue.segment, pos))

    inline def isTuple: Boolean = omEvaluatorValueIsATuple(evaluatorValue.segment)

    inline def tupleGetNumElements: Int = omEvaluatorTupleGetNumElements(evaluatorValue.segment).toInt

    inline def tupleGetElement(
      pos:         Int
    )(
      using arena: Arena
    ): EvaluatorValue = EvaluatorValue(omEvaluatorTupleGetElement(arena, evaluatorValue.segment, pos))

    inline def mapGetElement(
      map:         Attribute
    )(
      using arena: Arena
    ): EvaluatorValue = EvaluatorValue(omEvaluatorMapGetElement(arena, evaluatorValue.segment, map.segment))

    inline def mapGetKeys(
      using arena: Arena
    ): Attribute = new Attribute(omEvaluatorMapGetKeys(arena, evaluatorValue.segment))

    inline def isMap: Boolean = omEvaluatorValueIsAMap(evaluatorValue.segment)

    inline def mapGetType(
      using arena: Arena
    ): Type = new Type(omEvaluatorMapGetType(arena, evaluatorValue.segment))

    inline def isBasePath: Boolean = omEvaluatorValueIsABasePath(evaluatorValue.segment)

    inline def isPath: Boolean = omEvaluatorValueIsAPath(evaluatorValue.segment)

    inline def pathGetAsString(
      using arena: Arena
    ): Attribute = new Attribute(omEvaluatorPathGetAsString(arena, evaluatorValue.segment))

    inline def isReference: Boolean = omEvaluatorValueIsAReference(evaluatorValue.segment)

    inline def getReferenceValue(
      using arena: Arena
    ): EvaluatorValue = EvaluatorValue(omEvaluatorValueGetReferenceValue(arena, evaluatorValue.segment))

    inline def segment: MemorySegment = evaluatorValue._segment

    inline def sizeOf: Int = OMEvaluatorValue.sizeof().toInt

  inline def fromPrimitive(
    primitive:   Attribute
  )(
    using arena: Arena
  ): EvaluatorValue = EvaluatorValue(omEvaluatorValueFromPrimitive(arena, primitive.segment))

  extension (primitive: Attribute)
    inline def toEvaluatorValue(
      using arena: Arena
    ): EvaluatorValue = fromPrimitive(primitive)

  inline def basePathGetEmpty(
    using arena: Arena,
    context:     Context
  ): EvaluatorValue = EvaluatorValue(omEvaluatorBasePathGetEmpty(arena, context.segment))
end given

given ReferenceAttrApi with
  extension (attr: Attribute)
    inline def isReferenceAttr: Boolean = omAttrIsAReferenceAttr(attr.segment)
    inline def referenceAttrGetInnerRef(
      using arena: Arena
    ): Attribute = Attribute(omReferenceAttrGetInnerRef(arena, attr.segment))

given IntegerAttrApi with
  extension (attr: Attribute)
    inline def isIntegerAttr: Boolean = omAttrIsAIntegerAttr(attr.segment)
    inline def integerAttrGetInt(
      using arena: Arena
    ): Attribute = Attribute(omIntegerAttrGetInt(arena, attr.segment))
    inline def integerAttrGet(
      using arena: Arena
    ): Attribute = Attribute(omIntegerAttrGet(arena, attr.segment))
    inline def integerAttrToString(
      using arena: Arena
    ): String = omIntegerAttrToString(arena, attr.segment).toString

given ListAttrApi with
  extension (attr: Attribute)
    inline def isListAttr:             Boolean = omAttrIsAListAttr(attr.segment)
    inline def listAttrGetNumElements: Int     = omListAttrGetNumElements(attr.segment).toInt
    inline def listAttrGetElement(
      pos:         Int
    )(
      using arena: Arena
    ): Attribute = Attribute(omListAttrGetElement(arena, attr.segment, pos))

given MapAttrApi with
  extension (attr: Attribute)
    inline def isMapAttr:             Boolean = omAttrIsAMapAttr(attr.segment)
    inline def mapAttrGetNumElements: Int     = omMapAttrGetNumElements(attr.segment).toInt
    inline def mapAttrGetElementKey(
      pos:         Int
    )(
      using arena: Arena
    ): Identifier = Identifier(omMapAttrGetElementKey(arena, attr.segment, pos))
    inline def mapAttrGetElementValue(
      pos:         Int
    )(
      using arena: Arena
    ): Attribute = Attribute(omMapAttrGetElementValue(arena, attr.segment, pos))
