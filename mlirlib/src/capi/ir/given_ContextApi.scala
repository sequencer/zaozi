// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.ir

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{
  mlirContextAppendDialectRegistry,
  mlirContextCreate,
  mlirContextCreateWithRegistry,
  mlirContextCreateWithThreading,
  mlirContextDestroy,
  mlirContextEnableMultithreading,
  mlirContextGetOrLoadDialect,
  mlirContextLoadAllAvailableDialects,
  mlirContextSetAllowUnregisteredDialects,
  mlirContextSetThreadPool
}
import org.llvm.mlir.scalalib.capi.support.{*, given}

import java.lang.foreign.{Arena, MemorySegment}

given ContextApi with
  inline def contextCreate(
    using arena: Arena
  ): Context =
    Context(mlirContextCreate(arena))

  inline def contextCreateWithThreading(
    threadingEnabled: Boolean
  )(
    using arena:      Arena
  ): Context =
    Context(mlirContextCreateWithThreading(arena, threadingEnabled))

  inline def contextCreateWithRegistry(
    registry:         DialectRegistry,
    threadingEnabled: Boolean
  )(
    using arena:      Arena
  ): Context =
    Context(mlirContextCreateWithRegistry(arena, registry.segment, threadingEnabled))

  extension (context: Context)
    inline def getOrLoadDialect(
      name:        String
    )(
      using arena: Arena
    ): Dialect = Dialect(mlirContextGetOrLoadDialect(arena, context.segment, name.toStringRef.segment))
    inline def destroy():                                        Unit = mlirContextDestroy(context.segment)
    inline def allowUnregisteredDialects(allow: Boolean):        Unit =
      mlirContextSetAllowUnregisteredDialects(context.segment, allow)
    inline def appendDialectRegistry(registry: DialectRegistry): Unit =
      mlirContextAppendDialectRegistry(context.segment, registry.segment)
    inline def enableMultithreading(enable: Boolean):            Unit =
      mlirContextEnableMultithreading(context.segment, enable)
    inline def loadAllAvailableDialects():                       Unit =
      mlirContextLoadAllAvailableDialects(context.segment)
    inline def setThreadPool(threadPool: LlvmThreadPool):        Unit =
      mlirContextSetThreadPool(context.segment, threadPool.segment)

    inline def segment: MemorySegment = context._segment
    inline def sizeOf:  Int           = MlirContext.sizeof().toInt

end given
