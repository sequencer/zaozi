// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

// circt-c/Dialect/Comb.h
package org.llvm.circt.scalalib.comb.capi

import org.llvm.mlir.scalalib.Context

import java.lang.foreign.Arena

/** Comb Dialect API
  * {{{
  * mlirGetDialectHandle__comb__
  * registerCombPasses
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
