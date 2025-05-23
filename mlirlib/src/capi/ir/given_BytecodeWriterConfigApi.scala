// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.ir

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{
  mlirBytecodeWriterConfigCreate,
  mlirBytecodeWriterConfigDesiredEmitVersion,
  mlirBytecodeWriterConfigDestroy
}

import java.lang.foreign.{Arena, MemorySegment}

given BytecodeWriterConfigApi with
  inline def bytecodeWriterConfigCreate(
  )(
    using arena: Arena
  ) = BytecodeWriterConfig(mlirBytecodeWriterConfigCreate(arena))
  extension (bytecodeWriterConfig: BytecodeWriterConfig)
    inline def destroy():                         Unit          = mlirBytecodeWriterConfigDestroy(bytecodeWriterConfig.segment)
    inline def desiredEmitVersion(version: Long): Unit          =
      mlirBytecodeWriterConfigDesiredEmitVersion(bytecodeWriterConfig.segment, version)
    inline def segment:                           MemorySegment = bytecodeWriterConfig._segment
    inline def sizeOf:                            Int           = MlirBytecodeWriterConfig.sizeof().toInt
end given
