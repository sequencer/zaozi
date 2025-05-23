// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.ir

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{mlirAsmStateCreateForOperation, mlirAsmStateCreateForValue, mlirAsmStateDestroy}

import java.lang.foreign.{Arena, MemorySegment}

given AsmStateApi with
  inline def asmStateCreateForOperation(
    op:          Operation,
    flags:       OpPrintingFlags
  )(
    using arena: Arena
  ): MemorySegment = mlirAsmStateCreateForOperation(arena, op.segment, flags.segment)
  inline def asmStateCreateForValue(
    value:       Value,
    flags:       OpPrintingFlags
  )(
    using arena: Arena
  ): MemorySegment = mlirAsmStateCreateForValue(arena, value.segment, flags.segment)
  extension (asmState: AsmState)
    inline def destroy(): Unit          = mlirAsmStateDestroy(asmState.segment)
    inline def segment:   MemorySegment = asmState._segment
    inline def sizeOf:    Int           = MlirAsmState.sizeof().toInt
end given
