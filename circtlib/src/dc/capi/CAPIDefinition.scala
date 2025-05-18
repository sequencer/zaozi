// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

// circt-c/Dialect/DC.h
package org.llvm.circt.scalalib.dc.capi

import org.llvm.mlir.scalalib.Context

import java.lang.foreign.Arena

//
/** DC Dialect API
  * {{{
  * mlirGetDialectHandle__dc__
  * registerDCPasses
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
