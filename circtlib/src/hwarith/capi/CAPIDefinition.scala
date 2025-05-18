// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

// circt-c/Dialect/HWArith.h
package org.llvm.circt.scalalib.hwarith.capi

import org.llvm.mlir.scalalib.*

import java.lang.foreign.Arena

/** HWArith Dialect Api
  * {{{
  * mlirGetDialectHandle__hwarith__
  * registerHWArithPasses
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
