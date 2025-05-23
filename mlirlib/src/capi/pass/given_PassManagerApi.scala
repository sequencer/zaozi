// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.pass

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{
  mlirPassManagerAddOwnedPass,
  mlirPassManagerCreate,
  mlirPassManagerCreateOnOperation,
  mlirPassManagerDestroy,
  mlirPassManagerEnableIRPrinting,
  mlirPassManagerEnableVerifier,
  mlirPassManagerGetAsOpPassManager,
  mlirPassManagerGetNestedUnder,
  mlirPassManagerRunOnOp
}
import org.llvm.mlir.scalalib.capi.support.{*, given}
import org.llvm.mlir.scalalib.capi.ir.{*, given}

import java.lang.foreign.{Arena, MemorySegment}

given PassManagerApi with
  inline def passManagerCreate(
    using arena: Arena,
    context:     Context
  ): PassManager =
    PassManager(mlirPassManagerCreate(arena, context.segment))
  inline def passManagerCreateOnOperation(
    name:        String
  )(
    using arena: Arena,
    context:     Context
  ): PassManager = PassManager(mlirPassManagerCreateOnOperation(arena, context.segment, name.toStringRef.segment))
  extension (passManager: PassManager)
    inline def getAsOpPassManager(
      using arena: Arena
    ): OpPassManager = OpPassManager(mlirPassManagerGetAsOpPassManager(arena, passManager.segment))
    inline def runOnOp(
      operation:   Operation
    )(
      using arena: Arena
    ): LogicalResult = LogicalResult(mlirPassManagerRunOnOp(arena, passManager.segment, operation.segment))
    inline def getNestedUnder(
      operationName: String
    )(
      using arena:   Arena
    ): OpPassManager = OpPassManager(
      mlirPassManagerGetNestedUnder(arena, passManager.segment, operationName.toStringRef.segment)
    )
    inline def destroy(): Unit          = mlirPassManagerDestroy(passManager.segment)
    inline def enableIRPrinting(
      printBeforeAll:          Boolean,
      printAfterAll:           Boolean,
      printModuleScope:        Boolean,
      printAfterOnlyOnChange:  Boolean,
      printAfterOnlyOnFailure: Boolean,
      flags:                   OpPrintingFlags,
      treePrintingPath:        String
    )(
      using arena:             Arena
    ): Unit = mlirPassManagerEnableIRPrinting(
      passManager.segment,
      printBeforeAll,
      printAfterAll,
      printModuleScope,
      printAfterOnlyOnChange,
      printAfterOnlyOnFailure,
      flags.segment,
      treePrintingPath.toStringRef.segment
    )
    inline def enableVerifier(enable: Boolean): Unit = mlirPassManagerEnableVerifier(passManager.segment, enable)
    inline def addOwnedPass(
      pass: Pass
    ): Unit = mlirPassManagerAddOwnedPass(passManager.segment, pass.segment)
    inline def segment:   MemorySegment = passManager._segment
    inline def sizeOf:    Int           = MlirPassManager.sizeof().toInt
end given
