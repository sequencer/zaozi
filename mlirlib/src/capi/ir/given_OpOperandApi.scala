// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.ir

import org.llvm.mlir.*

import java.lang.foreign.{Arena, MemorySegment}

given OpOperandApi with
  extension (opOperandApi: OpOperand)
    inline def segment: MemorySegment = opOperandApi._segment
    inline def sizeOf:  Int           = MlirOpOperand.sizeof().toInt
end given
