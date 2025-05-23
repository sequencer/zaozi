// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.ir

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{
  mlirModuleCreateEmpty,
  mlirModuleCreateParse,
  mlirModuleDestroy,
  mlirModuleFromOperation,
  mlirModuleGetBody,
  mlirModuleGetContext,
  mlirModuleGetOperation
}
import org.llvm.mlir.scalalib.capi.support.{*, given}

import java.lang.foreign.{Arena, MemorySegment}

given ModuleApi with
  inline def moduleCreateEmpty(
    location:    Location
  )(
    using arena: Arena
  ): Module = new Module(mlirModuleCreateEmpty(arena, location.segment))

  inline def moduleCreateParse(
    module:      String | Array[Byte]
  )(
    using arena: Arena,
    context:     Context
  ): Module = new Module(
    mlirModuleCreateParse(
      arena,
      context.segment,
      (module match
        case string: String      => string.toStringRef
        case bytes:  Array[Byte] => bytes.toStringRef
      ).segment
    )
  )

  inline def moduleFromOperation(
    op:          Operation
  )(
    using arena: Arena
  ): Module = new Module(mlirModuleFromOperation(arena, op.segment))

  extension (module: Module)
    inline def getContext(
      using arena: Arena
    ): Context = Context(mlirModuleGetContext(arena, module.segment))
    inline def getBody(
      using arena: Arena
    ) = Block(mlirModuleGetBody(arena, segment))
    inline def getOperation(
      using arena: Arena
    ): Operation = Operation(mlirModuleGetOperation(arena, module.segment))
    inline def destroy(): Unit          = mlirModuleDestroy(module.segment)
    inline def segment:   MemorySegment = module._segment
    inline def sizeOf:    Int           = MlirModule.sizeof().toInt
end given
