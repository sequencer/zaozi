// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package org.llvm.mlir.scalalib.dialect.smt.capi

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{
  mlirGetDialectHandle__smt__,
  mlirSMTAttrCheckBVCmpPredicate,
  mlirSMTAttrCheckIntPredicate,
  mlirSMTAttrGetBVCmpPredicate,
  mlirSMTAttrGetBitVector,
  mlirSMTAttrGetIntPredicate,
  mlirSMTAttrIsASMTAttribute,
  mlirSMTTypeGetArray,
  mlirSMTTypeGetBitVector,
  mlirSMTTypeGetBool,
  mlirSMTTypeGetInt,
  mlirSMTTypeGetSMTFunc,
  mlirSMTTypeGetSort,
  mlirSMTTypeIsAArray,
  mlirSMTTypeIsABitVector,
  mlirSMTTypeIsABool,
  mlirSMTTypeIsAInt,
  mlirSMTTypeIsASMTFunc,
  mlirSMTTypeIsASort,
  mlirSMTTypeIsAnyNonFuncSMTValueType,
  mlirSMTTypeIsAnySMTValueType,
  mlirTranslateModuleToSMTLIB
}
import org.llvm.mlir.scalalib.capi.support.{*, given}
import org.llvm.mlir.scalalib.capi.ir.{Attribute, Block, Context, DialectHandle, Module, Type, given}

import java.lang.foreign.{Arena, MemorySegment}
import org.llvm.mlir.scalalib.capi.ir.given

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
  ): Type = Type(mlirSMTTypeGetArray(arena, context.segment, domainType.segment, rangeType.segment))
  inline def getBitVector(
    width:       Int
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(mlirSMTTypeGetBitVector(arena, context.segment, width))
  inline def getBool(
    using arena: Arena,
    context:     Context
  ): Type = Type(mlirSMTTypeGetBool(arena, context.segment))
  inline def getInt(
    using arena: Arena,
    context:     Context
  ): Type = Type(mlirSMTTypeGetInt(arena, context.segment))
  inline def getSMTFunc(
    domainTypes: Seq[Type],
    rangeType:   Type
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(
    mlirSMTTypeGetSMTFunc(arena, context.segment, domainTypes.length, domainTypes.toMlirArray, rangeType.segment)
  )
  inline def getSort(
    identifier:  String,
    sortParams:  Seq[Type]
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(
    mlirSMTTypeGetSort(
      arena,
      context.segment,
      identifier.identifierGet.segment,
      sortParams.length,
      sortParams.toMlirArray
    )
  )

  extension (tpe: Type)
    inline def isAnyNonFuncSMTValueType: Boolean = mlirSMTTypeIsAnyNonFuncSMTValueType(tpe.segment)
    inline def isAnySMTValueType:        Boolean = mlirSMTTypeIsAnySMTValueType(tpe.segment)
    inline def isArray:                  Boolean = mlirSMTTypeIsAArray(tpe.segment)
    inline def isBitVector:              Boolean = mlirSMTTypeIsABitVector(tpe.segment)
    inline def isBool:                   Boolean = mlirSMTTypeIsABool(tpe.segment)
    inline def isInt:                    Boolean = mlirSMTTypeIsAInt(tpe.segment)
    inline def isSMTFunc:                Boolean = mlirSMTTypeIsASMTFunc(tpe.segment)
    inline def isSort:                   Boolean = mlirSMTTypeIsASort(tpe.segment)

end given

given AttributeApi with
  extension (str:   String)
    inline def getBVCmpPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(mlirSMTAttrGetBVCmpPredicate(arena, context.segment, str.toStringRef.segment))
    inline def getIntPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(mlirSMTAttrGetIntPredicate(arena, context.segment, str.toStringRef.segment))
  extension (value: Int)
    inline def getBitVectorAttribute(
      width:       Int
    )(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(mlirSMTAttrGetBitVector(arena, context.segment, value, width))
  extension (attr:  Attribute) inline def isSMTAttribute: Boolean = mlirSMTAttrIsASMTAttribute(attr.segment)

  extension (str: String)
    inline def checkBVCmpPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Boolean = mlirSMTAttrCheckBVCmpPredicate(context.segment, str.toStringRef.segment)
    inline def checkIntPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Boolean = mlirSMTAttrCheckIntPredicate(context.segment, str.toStringRef.segment)
end given

given ModuleApi with
  extension (module: Module)
    inline def exportSMTLIB(
      callback:    String => Unit
    )(
      using arena: Arena
    ): Unit =
      LogicalResult(
        mlirTranslateModuleToSMTLIB(
          arena,
          module.segment,
          callback.stringToStringCallback.segment,
          MemorySegment.NULL,
          false,
          false
        )
      )
end given
