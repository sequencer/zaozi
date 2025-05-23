// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

// circt-c/Dialect/LLHD.h
package org.llvm.circt.scalalib.capi.dialect.llhd

import org.llvm.mlir.scalalib.capi.ir.{Attribute, Context, Type, given}

import java.lang.foreign.Arena

/** LLHD Dialect Api
  *
  * {{{
  * mlirGetDialectHandle__llhd__
  * }}}
  */
trait DialectApi:
  inline def loadDialect(
    using arena: Arena,
    context:     Context
  ): Unit
end DialectApi

/** LLHD Attribute API
  *
  * {{{
  * llhdAttrIsATimeAttr
  * llhdTimeAttrGet
  * llhdTimeAttrGetDelta
  * llhdTimeAttrGetEpsilon
  * llhdTimeAttrGetSeconds
  * llhdTimeAttrGetTimeUnit
  * }}}
  */
trait AttributeApi:
  extension (attribute: Attribute) def isTimeAttr(): Boolean
  def TimeAttrGet(
    timeUnit:    String,
    seconds:     BigInt,
    delta:       BigInt,
    epsilon:     BigInt
  )(
    using arena: Arena,
    context:     Context
  ): Attribute
  extension (attribute: Attribute)
    def TimeAttrGetDelta():   BigInt
    def TimeAttrGetEpsilon(): BigInt
    def TimeAttrGetSeconds(): BigInt
    def TimeAttrGetTimeUnit(
    )(
      using arena: Arena
    ):                        String
end AttributeApi

/** LLHD Type API
  *
  * {{{
  * llhdPointerTypeGet
  * llhdPointerTypeGetElementType
  * llhdSignalTypeGet
  * llhdSignalTypeGetElementType
  * llhdTypeIsAPointerType
  * llhdTypeIsASignalType
  * llhdTypeIsATimeType
  * }}}
  */
trait TypeApi:
  inline def pointerTypeGet(
    element:     Type
  )(
    using arena: Arena
  ): Type
  extension (tpe: Type)
    inline def pointerTypeGetElementType(
    )(
      using arena: Arena
    ):                        Type
    inline def signalTypeGet(
    )(
      using arena: Arena
    ):                        Type
    inline def signalTypeGetElementType(
    )(
      using arena: Arena
    ):                        Type
    inline def isPointerType: Boolean
    inline def isSignalType:  Boolean
    inline def isTimeType:    Boolean
end TypeApi
