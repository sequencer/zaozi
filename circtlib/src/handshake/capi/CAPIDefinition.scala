// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

// circt-c/Dialect/Handshake.h
package org.llvm.circt.scalalib.handshake.capi

import org.llvm.mlir.scalalib.*

import java.lang.foreign.Arena

/** Arc Dialect Api
  * {{{
  * mlirGetDialectHandle__handshake__
  * registerHandshakePasses
  * }}}
  */
trait DialectApi:
  extension (context: Context)
    inline def loadDialect(
    )(
      using arena: Arena
    ): Unit
  def registerPasses(): Unit
end DialectApi
