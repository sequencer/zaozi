// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package org.llvm.circt.scalalib.smt.capi

import org.llvm.circt.*
import org.llvm.circt.CAPI.*
import org.llvm.mlir.scalalib.{
  given_AttributeApi,
  Attribute,
  Context,
  DialectHandle,
  Identifier,
  LogicalResult,
  Module,
  PassManager,
  Type,
  given
}

import java.lang.foreign.{Arena, MemorySegment}

given DialectHandleApi with
  extension (context: Context)
    inline def loadSmtDialect(
    )(
      using arena: Arena
    ): Unit =
      DialectHandle(mlirGetDialectHandle__smt__(arena)).loadDialect(
        using arena,
        context
      )
end given

given TypeApi with
  inline def getArray(
    domainType:  Type,
    rangeType:   Type
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(smtTypeGetArray(arena, context.segment, domainType.segment, rangeType.segment))
  inline def getBitVector(
    width:       Int
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(smtTypeGetBitVector(arena, context.segment, width))
  inline def getBool(
    using arena: Arena,
    context:     Context
  ): Type = Type(smtTypeGetBool(arena, context.segment))
  inline def getInt(
    using arena: Arena,
    context:     Context
  ): Type = Type(smtTypeGetInt(arena, context.segment))
  inline def getSMTFunc(
    domainTypes: Seq[Type],
    rangeType:   Type
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(
    smtTypeGetSMTFunc(arena, context.segment, domainTypes.length, domainTypes.toMlirArray, rangeType.segment)
  )
  inline def getSort(
    identifier:  String,
    sortParams:  Seq[Type]
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(
    smtTypeGetSort(arena, context.segment, identifier.identifierGet.segment, sortParams.length, sortParams.toMlirArray)
  )

  extension (tpe: Type)
    inline def isAnyNonFuncSMTValueType: Boolean = smtTypeIsAnyNonFuncSMTValueType(tpe.segment)
    inline def isAnySMTValueType:        Boolean = smtTypeIsAnySMTValueType(tpe.segment)
    inline def isArray:                  Boolean = smtTypeIsAArray(tpe.segment)
    inline def isBitVector:              Boolean = smtTypeIsABitVector(tpe.segment)
    inline def isBool:                   Boolean = smtTypeIsABool(tpe.segment)
    inline def isInt:                    Boolean = smtTypeIsAInt(tpe.segment)
    inline def isSMTFunc:                Boolean = smtTypeIsASMTFunc(tpe.segment)
    inline def isSort:                   Boolean = smtTypeIsASort(tpe.segment)

end given

given AttributeApi with
  extension (str:   String)
    inline def getBVCmpPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(smtAttrGetBVCmpPredicate(arena, context.segment, str.toStringRef.segment))
    inline def getIntPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(smtAttrGetIntPredicate(arena, context.segment, str.toStringRef.segment))
  extension (value: Int)
    inline def getBitVectorAttribute(
      width:       Int
    )(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(smtAttrGetBitVector(arena, context.segment, value, width))
  extension (attr:  Attribute) inline def isSMTAttribute: Boolean = smtAttrIsASMTAttribute(attr.segment)

  extension (str: String)
    inline def checkBVCmpPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Boolean = smtAttrCheckBVCmpPredicate(context.segment, str.toStringRef.segment)
    inline def checkIntPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Boolean = smtAttrCheckIntPredicate(context.segment, str.toStringRef.segment)
end given

given ModuleApi with
  extension (module: Module)
    inline def exportSMTLIB(
      callback:    String => Unit
    )(
      using arena: Arena
    ): Unit =
      LogicalResult(
        mlirExportSMTLIB(arena, module.segment, callback.stringToStringCallback.segment, MemorySegment.NULL)
      )
end given
