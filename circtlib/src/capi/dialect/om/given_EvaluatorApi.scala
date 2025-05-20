// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Yuhang Zeng <unlsycn@unlsycn.com>
package org.llvm.circt.scalalib.capi.dialect.om

import org.llvm.circt.CAPI.{
  omEvaluatorBasePathGetEmpty,
  omEvaluatorGetModule,
  omEvaluatorInstantiate,
  omEvaluatorListGetElement,
  omEvaluatorListGetNumElements,
  omEvaluatorMapGetElement,
  omEvaluatorMapGetKeys,
  omEvaluatorMapGetType,
  omEvaluatorNew,
  omEvaluatorObjectGetField,
  omEvaluatorObjectGetFieldNames,
  omEvaluatorObjectGetHash,
  omEvaluatorObjectGetType,
  omEvaluatorObjectIsEq,
  omEvaluatorObjectIsNull,
  omEvaluatorPathGetAsString,
  omEvaluatorTupleGetElement,
  omEvaluatorTupleGetNumElements,
  omEvaluatorValueFromPrimitive,
  omEvaluatorValueGetContext,
  omEvaluatorValueGetLoc,
  omEvaluatorValueGetPrimitive,
  omEvaluatorValueGetReferenceValue,
  omEvaluatorValueIsABasePath,
  omEvaluatorValueIsAList,
  omEvaluatorValueIsAMap,
  omEvaluatorValueIsAObject,
  omEvaluatorValueIsAPath,
  omEvaluatorValueIsAPrimitive,
  omEvaluatorValueIsAReference,
  omEvaluatorValueIsATuple,
  omEvaluatorValueIsNull
}
import org.llvm.mlir.scalalib.given
import org.llvm.mlir.scalalib.{Attribute, Context, Location, Module, Type}

import java.lang.foreign.Arena

given EvaluatorApi with
  inline def basePathGetEmpty(
    using arena: Arena,
    context:     Context
  ): OMEvaluatorValue = OMEvaluatorValue(omEvaluatorBasePathGetEmpty(arena, context.segment))

  extension (evaluator: OMEvaluator)
    inline def getModule(
      using arena: Arena
    ): Module = new Module(omEvaluatorGetModule(arena, evaluator.segment))
    inline def instantiate(
      className:    String,
      actualParams: OMEvaluatorValue*
    )(
      using arena:  Arena,
      context:      Context
    ): OMEvaluatorValue =
      OMEvaluatorValue(
        omEvaluatorInstantiate(
          arena,
          evaluator.segment,
          className.stringAttrGet.segment,
          actualParams.length,
          actualParams.toMlirArray
        )
      )

  extension (evaluatorValue: OMEvaluatorValue)
    inline def listGetElement(
      pos:         Int
    )(
      using arena: Arena
    ): OMEvaluatorValue = OMEvaluatorValue(omEvaluatorListGetElement(arena, evaluatorValue.segment, pos))
    inline def listGetNumElements: Int = omEvaluatorListGetNumElements(evaluatorValue.segment).toInt
    inline def mapGetElement(
      map:         Attribute
    )(
      using arena: Arena
    ): OMEvaluatorValue = OMEvaluatorValue(omEvaluatorMapGetElement(arena, evaluatorValue.segment, map.segment))
    inline def mapGetKeys(
      using arena: Arena
    ): Attribute = new Attribute(omEvaluatorMapGetKeys(arena, evaluatorValue.segment))
    inline def mapGetType(
      using arena: Arena
    ): Type = new Type(omEvaluatorMapGetType(arena, evaluatorValue.segment))
  inline def evaluatorNew(
    module:      Module
  )(
    using arena: Arena
  ): OMEvaluator = OMEvaluator(omEvaluatorNew(arena, module.segment))
  extension (omObject:       OMEvaluatorValue)
    inline def objectGetField(
      name:        String
    )(
      using arena: Arena,
      context:     Context
    ): OMEvaluatorValue =
      OMEvaluatorValue(
        omEvaluatorObjectGetField(
          arena,
          omObject.segment,
          name.stringAttrGet.segment
        )
      )
    inline def objectGetFieldNames(
      using arena: Arena
    ): Attribute = new Attribute(omEvaluatorObjectGetFieldNames(arena, omObject.segment))
    inline def objectGetHash:                       Int     = omEvaluatorObjectGetHash(omObject.segment)
    inline def objectGetType(
      using arena: Arena
    ): Type = new Type(omEvaluatorObjectGetType(arena, omObject.segment))
    inline def objectIsEq(other: OMEvaluatorValue): Boolean =
      omEvaluatorObjectIsEq(omObject.segment, other.segment)
    inline def objectIsNull:                        Boolean = omEvaluatorObjectIsNull(omObject.segment)
  extension (evaluatorValue: OMEvaluatorValue)
    inline def pathGetAsString(
      using arena: Arena
    ): Attribute = new Attribute(omEvaluatorPathGetAsString(arena, evaluatorValue.segment))
    inline def tupleGetElement(
      pos:         Int
    )(
      using arena: Arena
    ): OMEvaluatorValue = OMEvaluatorValue(omEvaluatorTupleGetElement(arena, evaluatorValue.segment, pos))
    inline def tupleGetNumElements: Int = omEvaluatorTupleGetNumElements(evaluatorValue.segment).toInt
  inline def fromPrimitive(
    primitive:   Attribute
  )(
    using arena: Arena
  ): OMEvaluatorValue = OMEvaluatorValue(omEvaluatorValueFromPrimitive(arena, primitive.segment))
  extension (primitive:      Attribute)
    /** wrapper to [[fromPrimitive]] */
    inline def toEvaluatorValue(
      using arena: Arena
    ): OMEvaluatorValue = fromPrimitive(primitive)
  extension (evaluatorValue: OMEvaluatorValue)
    inline def getContext(
      using arena: Arena
    ): Context = Context(omEvaluatorValueGetContext(arena, evaluatorValue.segment))
    inline def getLoc(
      using arena: Arena
    ): Location = Location(omEvaluatorValueGetLoc(arena, evaluatorValue.segment))
    inline def getPrimitive(
      using arena: Arena
    ): Attribute = Attribute(omEvaluatorValueGetPrimitive(arena, evaluatorValue.segment))
    inline def getReferenceValue(
      using arena: Arena
    ): OMEvaluatorValue = OMEvaluatorValue(omEvaluatorValueGetReferenceValue(arena, evaluatorValue.segment))
    inline def isBasePath:  Boolean = omEvaluatorValueIsABasePath(evaluatorValue.segment)
    inline def isList:      Boolean = omEvaluatorValueIsAList(evaluatorValue.segment)
    inline def isMap:       Boolean = omEvaluatorValueIsAMap(evaluatorValue.segment)
    inline def isObject:    Boolean = omEvaluatorValueIsAObject(evaluatorValue.segment)
    inline def isPath:      Boolean = omEvaluatorValueIsAPath(evaluatorValue.segment)
    inline def isPrimitive: Boolean = omEvaluatorValueIsAPrimitive(evaluatorValue.segment)
    inline def isReference: Boolean = omEvaluatorValueIsAReference(evaluatorValue.segment)
    inline def isTuple:     Boolean = omEvaluatorValueIsATuple(evaluatorValue.segment)
    inline def isNull:      Boolean = omEvaluatorValueIsNull(evaluatorValue.segment)
end given
