// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

// circt-c/Dialect/SV.h
package org.llvm.circt.scalalib.capi.dialect.sv

import org.llvm.mlir.scalalib.*

import java.lang.foreign.Arena

/** SV Dialect API
  * {{{
  * mlirGetDialectHandle__sv__
  * registerSVPasses
  * }}}
  */
trait DialectApi:
  inline def loadDialect(
    using arena: Arena,
    context:     Context
  ):                  Unit
  def registerPasses: Unit
end DialectApi
