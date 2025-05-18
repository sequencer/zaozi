// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

// circt-c/Dialect/Debug.h
package org.llvm.circt.scalalib.debug.capi

import org.llvm.mlir.scalalib.Context

import java.lang.foreign.Arena

/** Debug Dialect API
  * {{{
  * mlirGetDialectHandle__debug__
  * }}}
  */

trait DialectApi:
  extension (context: Context)
    inline def loadDialect(
    )(
      using arena: Arena
    ): Unit
end DialectApi
