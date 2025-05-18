// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.comb.capi

import org.llvm.circt.CAPI.{mlirGetDialectHandle__comb__ as mlirGetDialectHandle, registerCombPasses as r}
import org.llvm.mlir.scalalib.{Context, DialectHandle, given}

import java.lang.foreign.Arena

given DialectApi with
  extension (context: Context)
    inline def loadDialect(
    )(
      using arena: Arena
    ): Unit =
      DialectHandle(mlirGetDialectHandle(arena)).loadDialect(
        using arena,
        context
      )
  def registerPasses(): Unit = r()
end given
