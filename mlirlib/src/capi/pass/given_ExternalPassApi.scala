// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.pass

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{mlirCreateExternalPass, mlirExternalPassSignalFailure}
import org.llvm.mlir.scalalib.capi.support.{*, given}
import org.llvm.mlir.scalalib.capi.ir.{*, given}

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

given ExternalPassCallbacksApi with
  inline def createExternalPassCallbacks(
    constructCallback:  () => Unit,
    destructCallback:   () => Unit,
    initializeCallback: Option[Context => LogicalResult],
    cloneCallback:      () => Unit,
    runCallback:        (Operation, ExternalPass) => Unit
  )(
    using arena:        Arena
  ): ExternalPassCallbacks =
    val segment = MlirExternalPassCallbacks.allocate(arena)
    MlirExternalPassCallbacks.construct$set(
      segment,
      MlirExternalPassCallbacks.construct.allocate((nil: MemorySegment) => constructCallback(), arena)
    )
    MlirExternalPassCallbacks.destruct$set(
      segment,
      MlirExternalPassCallbacks.destruct.allocate((nil: MemorySegment) => destructCallback(), arena)
    )
    initializeCallback.foreach(initializeCallback =>
      MlirExternalPassCallbacks.initialize$set(
        segment,
        MlirExternalPassCallbacks.initialize
          .allocate((context: MemorySegment, nil: MemorySegment) => initializeCallback(Context(context)).segment, arena)
      )
    )
    MlirExternalPassCallbacks.clone$set(
      segment,
      MlirExternalPassCallbacks.clone.allocate(
        (nil: MemorySegment) =>
          cloneCallback()
          // see https://mlir.llvm.org/doxygen/CAPI_2IR_2Pass_8cpp_source.html#l00178, clonedUserData set to null
          MemorySegment.NULL
        ,
        arena
      )
    )
    MlirExternalPassCallbacks.run$set(
      segment,
      MlirExternalPassCallbacks.run.allocate(
        (operation: MemorySegment, externalPass: MemorySegment, userData: MemorySegment) =>
          runCallback(Operation(operation), ExternalPass(externalPass)),
        arena
      )
    )
    ExternalPassCallbacks(segment)
  extension (pass: ExternalPassCallbacks)
    inline def signalFailure(): Unit          = mlirExternalPassSignalFailure(pass.segment)
    inline def segment:         MemorySegment = pass._segment
    inline def sizeOf:          Int           = MlirExternalPassCallbacks.sizeof().toInt
end given
