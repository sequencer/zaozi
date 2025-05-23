// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.support

import org.llvm.mlir.*

import java.lang.foreign.MemorySegment

given TypeIDApi with
  extension (typeID: TypeID)
    inline def segment: MemorySegment = typeID._segment
    inline def sizeOf:  Int           = MlirTypeID.sizeof().toInt
end given
