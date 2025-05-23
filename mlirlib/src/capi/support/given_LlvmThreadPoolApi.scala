// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.support

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{mlirLlvmThreadPoolCreate, mlirLlvmThreadPoolDestroy}

import java.lang.foreign.{Arena, MemorySegment}

given LlvmThreadPoolApi with
  inline def llvmThreadPoolCreate(
  )(
    using arena: Arena
  ): LlvmThreadPool = LlvmThreadPool(mlirLlvmThreadPoolCreate(arena))
  extension (llvmThreadPool: LlvmThreadPool)
    inline def destroy(): Unit          = mlirLlvmThreadPoolDestroy(llvmThreadPool.segment)
    inline def segment:   MemorySegment = llvmThreadPool._segment
    inline def sizeOf:    Int           = MlirLlvmThreadPool.sizeof().toInt
end given
