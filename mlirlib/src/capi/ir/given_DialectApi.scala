// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.ir

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{
  mlirDialectHandleGetNamespace,
  mlirDialectHandleInsertDialect,
  mlirDialectHandleLoadDialect,
  mlirDialectHandleRegisterDialect,
  mlirGetDialectHandle__func__
}
import org.llvm.mlir.scalalib.capi.support.{*, given}

import java.lang.foreign.{Arena, MemorySegment}

given DialectApi with
  extension (dialect: Dialect)
    inline def segment: MemorySegment = dialect._segment
    inline def sizeOf:  Int           = MlirDialect.sizeof().toInt
end given

given DialectHandleApi with
  extension (dialectHandle: DialectHandle)
    inline def getNamespace(
      using arena: Arena
    ): String = StringRef(mlirDialectHandleGetNamespace(arena, dialectHandle.segment)).toScalaString
    inline def loadDialect(
      using arena: Arena,
      context:     Context
    ): Unit = mlirDialectHandleLoadDialect(arena, dialectHandle.segment, context.segment)
    inline def insertDialect(dialectRegistry: DialectRegistry): Unit          =
      mlirDialectHandleInsertDialect(dialectHandle.segment, dialectRegistry.segment)
    inline def insertDialect(
    )(
      using context: Context
    ): Unit =
      mlirDialectHandleRegisterDialect(dialectHandle.segment, context.segment)
    inline def segment:                                         MemorySegment = dialectHandle._segment
    inline def sizeOf:                                          Int           = MlirDialectHandle.sizeof().toInt
end given
