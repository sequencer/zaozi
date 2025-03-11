// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.emit.capi

import org.llvm.circt.CAPI.*
import org.llvm.mlir.scalalib.{Context, DialectHandle, given}

import java.lang.foreign.Arena

given DialectHandleApi with
  extension (context: Context)
    inline def loadEmitDialect(
    )(
      using arena: Arena
    ): Unit =
      DialectHandle(mlirGetDialectHandle__emit__(arena)).loadDialect(
        using arena,
        context
      )
end given
