// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.smt.capi

import org.llvm.mlir.scalalib.*

import java.lang.foreign.{Arena, MemorySegment}

trait DialectHandleApi:
  extension (context: Context)
    inline def loadSmtDialect(
    )(
      using arena: Arena
    ): Unit
end DialectHandleApi