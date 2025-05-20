// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

// circt-c/Dialect/Verif.h
package org.llvm.circt.scalalib.capi.dialect.verif

import org.llvm.mlir.scalalib.*

import java.lang.foreign.Arena

/** Arc Dialect Api
  * {{{
  * mlirGetDialectHandle__verif__
  * registerArcPasses
  * }}}
  */
trait DialectApi:
  inline def loadDialect(
    using arena: Arena,
    context:     Context
  ): Unit
end DialectApi
