// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Yuhang Zeng <unlsycn@unlsycn.com>
package org.llvm.circt.scalalib.om.capi

import org.llvm.mlir.scalalib.*

import java.lang.foreign.{Arena, MemorySegment}

trait DialectHandleApi:
  extension (context: Context)
    inline def loadOmDialect(
    )(
      using arena: Arena
    ): Unit
end DialectHandleApi

trait TypeApi:
  extension (tpe: Type)
    inline def isAAnyType:            Boolean
    inline def isAClassType:          Boolean
    inline def isAFrozenBasePathType: Boolean
    inline def isAFrozenPathType:     Boolean
    inline def isAListType:           Boolean
    inline def isAMapType:            Boolean
    inline def isAStringType:         Boolean
    inline def classTypeGetName(
      using arena: Arena
    ):                                Identifier
    inline def listTypeGetElementType(
      using arena: Arena
    ):                                Type
    inline def mapTypeGetKeyType(
      using arena: Arena
    ):                                Type

  inline def anyTypeGetTypeID(
    using arena: Arena
  ): TypeID
  inline def classTypeGetTypeID(
    using arena: Arena
  ): TypeID
  inline def frozenBasePathTypeGetTypeID(
    using arena: Arena
  ): TypeID
  inline def frozenPathTypeGetTypeID(
    using arena: Arena
  ): TypeID
  inline def listTypeGetTypeID(
    using arena: Arena
  ): TypeID
end TypeApi

class Evaluator(val _segment: MemorySegment)
class EvaluatorValue(val _segment: MemorySegment)

trait EvaluatorApi extends HasSegment[Evaluator]:
  inline def evaluatorNew(
    module:      Module
  )(
    using arena: Arena
  ): Evaluator

  extension (evaluator: Evaluator)
    inline def instantiate(
      className:    Attribute,
      actualParams: EvaluatorValue*
    )(
      using arena:  Arena
    ): EvaluatorValue

    inline def getModule(
      using arena: Arena
    ): Module
end EvaluatorApi

trait ObjectApi:
  extension (evaluatorValue: EvaluatorValue)
    inline def objectIsNull:  Boolean
    inline def objectGetType(
      using arena: Arena
    ):                        Type
    inline def objectGetField(
      name:        Attribute
    )(
      using arena: Arena
    ):                        EvaluatorValue
    inline def objectGetHash: Int
    inline def objectIsEq(
      other: EvaluatorValue
    ):                        Boolean
    inline def objectGetFieldNames(
      using arena: Arena
    ):                        Attribute
end ObjectApi

trait EvaluatorValueApi extends HasSegment[EvaluatorValue] with HasSizeOf[EvaluatorValue]:
  extension (evaluatorValue: EvaluatorValue)
    inline def getContext(
      using arena: Arena
    ):                              Context
    inline def getLoc(
      using arena: Arena
    ):                              Location
    inline def isNull:              Boolean
    inline def isAObject:           Boolean
    inline def isAPrimitive:        Boolean
    inline def getPrimitive(
      using arena: Arena
    ):                              Attribute
    // TODO: add CAPI to get MlirType of a list
    inline def isAList:             Boolean
    inline def listGetNumElements:  Int
    inline def listGetElement(
      pos:         Int
    )(
      using arena: Arena
    ):                              EvaluatorValue
    inline def isATuple:            Boolean
    inline def tupleGetNumElements: Int
    inline def tupleGetElement(
      pos:         Int
    )(
      using arena: Arena
    ):                              EvaluatorValue
    inline def mapGetElement(
      map:         Attribute
    )(
      using arena: Arena
    ):                              EvaluatorValue
    inline def mapGetKeys(
      using arena: Arena
    ):                              Attribute
    inline def isAMap:              Boolean
    inline def mapGetType(
      using arena: Arena
    ):                              Type
    inline def isABasePath:         Boolean
    inline def isAPath:             Boolean
    inline def pathGetAsString(
      using arena: Arena
    ):                              Attribute
    inline def isAReference:        Boolean
    inline def getReferenceValue(
      using arena: Arena
    ):                              EvaluatorValue

  inline def fromPrimitive(
    primitive:   Attribute
  )(
    using arena: Arena
  ): EvaluatorValue

  inline def basePathGetEmpty(
    using arena: Arena,
    context:     Context
  ): EvaluatorValue
end EvaluatorValueApi

trait ReferenceAttrApi:
  extension (attr: Attribute)
    inline def isAReferenceAttr: Boolean
    inline def referenceAttrGetInnerRef(
      using arena: Arena
    ):                           Attribute
end ReferenceAttrApi

trait IntegerAttrApi:
  extension (attr: Attribute)
    inline def isAIntegerAttr: Boolean
    inline def integerAttrGetInt(
      using arena: Arena
    ):                         Attribute
    inline def integerAttrGet(
      using arena: Arena
    ):                         Attribute
    inline def integerAttrToString(
      using arena: Arena
    ):                         String
end IntegerAttrApi

trait ListAttrApi:
  extension (attr: Attribute)
    inline def isAListAttr:            Boolean
    inline def listAttrGetNumElements: Int
    inline def listAttrGetElement(
      pos:         Int
    )(
      using arena: Arena
    ):                                 Attribute
end ListAttrApi

trait MapAttrApi:
  extension (attr: Attribute)
    inline def isAMapAttr:            Boolean
    inline def mapAttrGetNumElements: Int
    inline def mapAttrGetElementKey(
      pos:         Int
    )(
      using arena: Arena
    ):                                Identifier
    inline def mapAttrGetElementValue(
      pos:         Int
    )(
      using arena: Arena
    ):                                Attribute
end MapAttrApi
