// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.emit.capi

// circt-c/Dialect/Esi.h
import org.llvm.mlir.scalalib.Context

import java.lang.foreign.Arena

trait DialectApi:
  extension (context: Context)
    inline def loadDialect(
    )(
      using arena: Arena
    ): Unit
end DialectApi
