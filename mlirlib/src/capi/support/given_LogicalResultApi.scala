// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.support

import org.llvm.mlir.*

import java.lang.foreign.MemorySegment

given LogicalResultApi with
  extension (logicalResult: LogicalResult)
    inline def segment: MemorySegment = logicalResult._segment
    inline def sizeOf:  Int           = MlirLogicalResult.sizeof().toInt
end given
