// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package org.llvm.circt.scalalib.smt.capi

import org.llvm.mlir.scalalib.*

import java.lang.foreign.{Arena, MemorySegment}

trait DialectHandleApi:
  extension (context: Context)
    inline def loadSmtDialect(
    )(
      using arena: Arena
    ): Unit
end DialectHandleApi

trait TypeApi:
  inline def getArray(
    domainType:  Type,
    rangeType:   Type
  )(
    using arena: Arena,
    context:     Context
  ): Type
  inline def getBitVector(
    width:       Int
  )(
    using arena: Arena,
    context:     Context
  ): Type
  inline def getBool(
    using arena: Arena,
    context:     Context
  ): Type
  inline def getInt(
    using arena: Arena,
    context:     Context
  ): Type
  inline def getSMTFunc(
    domainTypes: Seq[Type],
    rangeType:   Type
  )(
    using arena: Arena,
    context:     Context
  ): Type
  inline def getSort(
    identifier:  String,
    sortParams:  Seq[Type]
  )(
    using arena: Arena,
    context:     Context
  ): Type
  extension (tpe: Type)
    inline def isAnyNonFuncSMTValueType: Boolean
    inline def isAnySMTValueType:        Boolean
    inline def isArray:                  Boolean
    inline def isBitVector:              Boolean
    inline def isBool:                   Boolean
    inline def isInt:                    Boolean
    inline def isSMTFunc:                Boolean
    inline def isSort:                   Boolean
end TypeApi

trait AttributeApi:
  extension (str:   String)
    inline def getBVCmpPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute
    inline def getIntPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (value: Int)
    inline def getBitVectorAttribute(
      width:       Int
    )(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (attr:  Attribute) inline def isSMTAttribute: Boolean
  extension (str:   String)
    inline def checkBVCmpPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Boolean
    inline def checkIntPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Boolean
end AttributeApi

trait ModuleApi:
  extension (module: Module)
    inline def exportSMTLIB(
      callBack:    String => Unit
    )(
      using arena: Arena
    ): Unit
end ModuleApi
