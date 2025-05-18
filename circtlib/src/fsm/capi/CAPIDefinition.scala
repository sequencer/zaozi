// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

// circt-c/Dialect/FSM.h
package org.llvm.circt.scalalib.fsm.capi

import org.llvm.mlir.scalalib.*

import java.lang.foreign.Arena

/** FSM Dialect API
  * {{{
  * mlirGetDialectHandle__fsm__
  * registerFsmPasses
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
