// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.ir

import org.llvm.mlir.*

import java.lang.foreign.MemorySegment

given SymbolTableApi with
  extension (symbolTableApi: SymbolTable)
    inline def segment: MemorySegment = symbolTableApi._segment
    inline def sizeOf:  Int           = MlirSymbolTable.sizeof().toInt
end given
