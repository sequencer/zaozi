// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

// circt-c/Dialect/Seq.h
package org.llvm.circt.scalalib.capi.dialect.seq

import org.llvm.mlir.scalalib.*

import java.lang.foreign.Arena

/** Seq Dialect Api
  *
  * {{{
  * mlirGetDialectHandle__seq__
  * registerSeqPasses
  * }}}
  */
trait DialectApi:
  inline def loadDialect(
    using arena: Arena,
    context:     Context
  ):                  Unit
  def registerPasses: Unit
end DialectApi

/** Seq Type API
  *
  * {{{
  * seqClockTypeGet
  * seqImmutableTypeGet
  * seqImmutableTypeGetInnerType
  * seqTypeIsAClock
  * seqTypeIsAImmutable
  * }}}
  */
trait TypeApi:
  def clockTypeGet(
    using arena: Arena,
    context:     Context
  ): Type
  def immutableTypeGet(
    tpe:         Type
  )(
    using arena: Arena
  ): Type
  def immutableTypeGetInnerType(
    tpe:         Type
  )(
    using arena: Arena
  ): Type
  extension (tpe: Type)
    def isClock:     Boolean
    def isImmutable: Boolean
end TypeApi
