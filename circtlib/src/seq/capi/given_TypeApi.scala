// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.seq.capi

import org.llvm.circt.CAPI.seqClockTypeGet
import org.llvm.circt.CAPI.seqImmutableTypeGet
import org.llvm.circt.CAPI.seqImmutableTypeGetInnerType
import org.llvm.circt.CAPI.seqTypeIsAClock
import org.llvm.circt.CAPI.seqTypeIsAImmutable
import org.llvm.mlir.scalalib.Type
import org.llvm.mlir.scalalib.{Context, DialectHandle, given}

import java.lang.foreign.Arena

given TypeApi with
  def clockTypeGet(
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(seqClockTypeGet(arena, context.segment))
  def immutableTypeGet(
    tpe:         Type
  )(
    using arena: Arena
  ): Type = Type(seqImmutableTypeGet(arena, tpe.segment))
  def immutableTypeGetInnerType(
    tpe:         Type
  )(
    using arena: Arena
  ): Type = Type(seqImmutableTypeGetInnerType(arena, tpe.segment))
  extension (tpe: Type)
    def isClock():     Boolean = seqTypeIsAClock(tpe.segment)
    def isImmutable(): Boolean = seqTypeIsAImmutable(tpe.segment)
end given
