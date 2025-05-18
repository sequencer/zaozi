// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.llhd.capi

import org.llvm.circt.CAPI.llhdAttrIsATimeAttr
import org.llvm.circt.CAPI.llhdTimeAttrGet
import org.llvm.circt.CAPI.llhdTimeAttrGetDelta
import org.llvm.circt.CAPI.llhdTimeAttrGetEpsilon
import org.llvm.circt.CAPI.llhdTimeAttrGetSeconds
import org.llvm.circt.CAPI.llhdTimeAttrGetTimeUnit
import org.llvm.circt.CAPI.mlirGetDialectHandle__llhd__ as mlirGetDialectHandle
import org.llvm.mlir.scalalib.Attribute
import org.llvm.mlir.scalalib.StringRef
import org.llvm.mlir.scalalib.{Context, DialectHandle, given}

import java.lang.foreign.Arena

given AttributeApi with
  extension (attribute: Attribute) def isTimeAttr(): Boolean = llhdAttrIsATimeAttr(attribute.segment)
  def TimeAttrGet(
    timeUnit:    String,
    seconds:     BigInt,
    delta:       BigInt,
    epsilon:     BigInt
  )(
    using arena: Arena,
    context:     Context
  ): Attribute = Attribute(
    llhdTimeAttrGet(arena, context.segment, timeUnit.toStringRef.segment, seconds.toLong, delta.toLong, epsilon.toLong)
  )
  extension (attribute: Attribute)
    def TimeAttrGetDelta():   BigInt = llhdTimeAttrGetDelta(attribute.segment)
    def TimeAttrGetEpsilon(): BigInt = llhdTimeAttrGetEpsilon(attribute.segment)
    def TimeAttrGetSeconds(): BigInt = llhdTimeAttrGetSeconds(attribute.segment)
    def TimeAttrGetTimeUnit(
    )(
      using arena: Arena
    ): String = StringRef(llhdTimeAttrGetTimeUnit(arena, attribute.segment)).toScalaString
end given
