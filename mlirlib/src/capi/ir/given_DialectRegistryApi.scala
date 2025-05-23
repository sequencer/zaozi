// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.ir

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{mlirDialectRegistryCreate, mlirDialectRegistryDestroy}

import java.lang.foreign.{Arena, MemorySegment}

given DialectRegistryApi with
  inline def registryCreate(
  )(
    using arena: Arena
  ): DialectRegistry = DialectRegistry(mlirDialectRegistryCreate(arena))

  extension (dialectRegistry: DialectRegistry)
    inline def destroy(): Unit          = mlirDialectRegistryDestroy(dialectRegistry.segment)
    inline def segment:   MemorySegment = dialectRegistry._segment
    inline def sizeOf:    Int           = MlirDialectRegistry.sizeof().toInt
end given
