// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.emit.capi

import org.llvm.circt.CAPI.mlirGetDialectHandle__emit__ as mlirGetDialectHandle
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
end given
