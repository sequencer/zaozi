// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package org.llvm.mlir.scalalib.capi.dialect.smt

import org.llvm.mlir.*

import org.llvm.mlir.CAPI.{
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
  mlirSMTTypeIsAnySMTValueType
}

import org.llvm.mlir.scalalib.capi.support.{*, given}
import org.llvm.mlir.scalalib.capi.ir.{Context, Type, given}

import java.lang.foreign.Arena

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
