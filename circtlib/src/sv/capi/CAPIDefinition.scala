// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.sv.capi

import org.llvm.mlir.scalalib.*

import java.lang.foreign.Arena

trait DialectHandleApi:
  extension (context: Context)
    inline def loadSvDialect(
    )(
      using arena: Arena
    ): Unit
end DialectHandleApi
