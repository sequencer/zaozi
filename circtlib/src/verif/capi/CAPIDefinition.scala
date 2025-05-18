// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

// circt-c/Dialect/Verif.h
package org.llvm.circt.scalalib.verif.capi

import org.llvm.mlir.scalalib.*

import java.lang.foreign.Arena

/** Arc Dialect Api
  * {{{
  * mlirGetDialectHandle__verif__
  * registerArcPasses
  * }}}
  */
trait DialectApi:
  extension (context: Context)
    inline def loadDialect(
    )(
      using arena: Arena
    ): Unit
end DialectApi
