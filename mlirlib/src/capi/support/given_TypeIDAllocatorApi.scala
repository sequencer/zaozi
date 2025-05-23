// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.support

import org.llvm.mlir.*

import java.lang.foreign.MemorySegment

given TypeIDAllocatorApi with
  extension (typeIDAllocator: TypeIDAllocator)
    inline def segment: MemorySegment = typeIDAllocator._segment
    inline def sizeOf:  Int           = MlirTypeIDAllocator.sizeof().toInt
end given
