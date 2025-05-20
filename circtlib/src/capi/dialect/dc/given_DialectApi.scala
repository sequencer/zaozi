// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.dialect.dc

import org.llvm.circt.CAPI.{mlirGetDialectHandle__dc__ as mlirGetDialectHandle, registerDCPasses as r}
import org.llvm.mlir.scalalib.given
import org.llvm.mlir.scalalib.{Context, DialectHandle}

import java.lang.foreign.Arena

given DialectApi with
  inline def loadDialect(
    using arena: Arena,
    context:     Context
  ): Unit =
    DialectHandle(mlirGetDialectHandle(arena)).loadDialect(
      using arena,
      context
    )
  def registerPasses: Unit = r()
end given
