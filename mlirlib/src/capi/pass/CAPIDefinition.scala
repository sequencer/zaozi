// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.pass

import org.llvm.mlir.scalalib.capi.support.{*, given}
import org.llvm.mlir.scalalib.capi.ir.{*, given}

import java.lang.foreign.{Arena, MemorySegment}

class Pass(val _segment: MemorySegment)
trait PassApi extends HasSegment[Pass] with HasSizeOf[Pass]:
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
  ): Pass

end PassApi

class ExternalPass(val _segment: MemorySegment)
trait ExternalPassApi extends HasSegment[ExternalPass] with HasSizeOf[ExternalPass]

class PassManager(val _segment: MemorySegment)
trait PassManagerApi extends HasSegment[PassManager] with HasSizeOf[PassManager]:
  inline def passManagerCreate(
    using arena: Arena,
    context:     Context
  ): PassManager

  inline def passManagerCreateOnOperation(
    name:        String
  )(
    using arena: Arena,
    context:     Context
  ): PassManager

  extension (passManager: PassManager)
    inline def getAsOpPassManager(
      using arena: Arena
    ):                                          OpPassManager
    inline def runOnOp(
      operation:   Operation
    )(
      using arena: Arena
    ):                                          LogicalResult
    inline def getNestedUnder(
      operationName: String
    )(
      using arena:   Arena
    ):                                          OpPassManager
    inline def destroy():                       Unit
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
    ):                                          Unit
    inline def enableVerifier(enable: Boolean): Unit
    inline def addOwnedPass(
      pass: Pass
    ):                                          Unit

end PassManagerApi

class OpPassManager(val _segment: MemorySegment)
trait OpPassManagerApi extends HasSegment[OpPassManager] with HasSizeOf[OpPassManager]:
  extension (opPassManager: OpPassManager)
    inline def getNestedUnder(
      passManager:   PassManager,
      operationName: String
    )(
      using arena:   Arena
    ): OpPassManager
    inline def addPipeline(
      pipelineElements: String,
      callback:         String => Unit
    )(
      using arena:      Arena
    ): LogicalResult
    inline def parsePassPipeline(
      pipeline:    String,
      callback:    String => Unit
    )(
      using arena: Arena
    ): LogicalResult
    inline def addOwnedPass(
      pass: Pass
    ): Unit
end OpPassManagerApi

class ExternalPassCallbacks(val _segment: MemorySegment)
trait ExternalPassCallbacksApi extends HasSegment[ExternalPassCallbacks] with HasSizeOf[ExternalPassCallbacks]
