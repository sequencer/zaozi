// SPDX-License-Identifier: Apache-2.0
package org.llvm.mlir.scalalib

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.*

import java.lang.foreign.{Arena, MemorySegment}

given PassApi with
  inline def createExternalPass(
    passId:            TypeID,
    name:              String,
    argument:          String,
    description:       String,
    opName:            String,
    dependentDialects: Seq[DialectHandle],
    callbacks:         ExternalPassCallbacks
  )(
    using arena:       Arena
  ): Pass =
    Pass(
      mlirCreateExternalPass(
        arena,
        passId.segment,
        name.toStringRef.segment,
        argument.toStringRef.segment,
        description.toStringRef.segment,
        opName.toStringRef.segment,
        dependentDialects.size,
        dependentDialects.toMlirArray,
        callbacks.segment,
        MemorySegment.NULL
      )
    )

  extension (pass: Pass)
    inline def segment: MemorySegment = pass._segment
    inline def sizeOf:  Int           = MlirPass.sizeof().toInt
end given

given ExternalPassApi with
  extension (pass: ExternalPass)
    inline def signalFailure(): Unit          = mlirExternalPassSignalFailure(pass.segment)
    inline def segment:         MemorySegment = pass._segment
    inline def sizeOf:          Int           = MlirExternalPass.sizeof().toInt
end given

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
    )(
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
      printAfterOnlyOnFailure: Boolean
    ): Unit = mlirPassManagerEnableIRPrinting(
      passManager.segment,
      printBeforeAll,
      printAfterAll,
      printModuleScope,
      printAfterOnlyOnChange,
      printAfterOnlyOnFailure
    )
    inline def enableVerifier(enable: Boolean): Unit = mlirPassManagerEnableVerifier(passManager.segment, enable)
    inline def addOwnedPass(
      pass: Pass
    ): Unit = mlirPassManagerAddOwnedPass(passManager.segment, pass.segment)
    inline def segment:   MemorySegment = passManager._segment
    inline def sizeOf:    Int           = MlirPassManager.sizeof().toInt
end given

given OpPassManagerApi with
  extension (opPassManager: OpPassManager)
    inline def getNestedUnder(
      passManager:   PassManager,
      operationName: String
    )(
      using arena:   Arena
    ): OpPassManager =
      OpPassManager(mlirOpPassManagerGetNestedUnder(arena, passManager.segment, operationName.toStringRef.segment))
    inline def addPipeline(
      pipelineElements: String,
      callback:         String => Unit
    )(
      using arena:      Arena
    ): LogicalResult =
      LogicalResult(
        mlirOpPassManagerAddPipeline(
          arena,
          opPassManager.segment,
          pipelineElements.toStringRef.segment,
          callback.stringToStringCallback.segment,
          MemorySegment.NULL
        )
      )
    inline def parsePassPipeline(
      pipeline:    String,
      callback:    String => Unit
    )(
      using arena: Arena
    ): LogicalResult = LogicalResult(
      mlirParsePassPipeline(
        arena,
        opPassManager.segment,
        pipeline.toStringRef.segment,
        callback.stringToStringCallback.segment,
        MemorySegment.NULL
      )
    )
    inline def addOwnedPass(
      pass: Pass
    ): Unit = mlirOpPassManagerAddOwnedPass(opPassManager.segment, pass.segment)
    inline def printPassPipeline(
      callback:    String => Unit
    )(
      using arena: Arena
    ): Unit = mlirPrintPassPipeline(opPassManager.segment, callback.stringToStringCallback.segment, MemorySegment.NULL)
    inline def segment: MemorySegment = opPassManager._segment
    inline def sizeOf:  Int           = MlirOpPassManager.sizeof().toInt
end given
