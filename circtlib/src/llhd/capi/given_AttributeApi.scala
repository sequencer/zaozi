// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.llhd.capi

import org.llvm.circt.CAPI.{
  llhdAttrIsATimeAttr,
  llhdTimeAttrGet,
  llhdTimeAttrGetDelta,
  llhdTimeAttrGetEpsilon,
  llhdTimeAttrGetSeconds,
  llhdTimeAttrGetTimeUnit
}
import org.llvm.mlir.scalalib.given
import org.llvm.mlir.scalalib.{Attribute, Context, StringRef}

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
