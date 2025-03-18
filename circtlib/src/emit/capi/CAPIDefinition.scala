// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.emit.capi

import org.llvm.mlir.scalalib.*

import java.lang.foreign.Arena

trait DialectHandleApi:
  extension (context: Context)
    inline def loadEmitDialect(
    )(
      using arena: Arena
    ): Unit
end DialectHandleApi
