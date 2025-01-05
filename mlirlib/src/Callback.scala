// SPDX-License-Identifier: Apache-2.0
package org.llvm.mlir.scalalib

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.mlirExternalPassSignalFailure

import java.lang.foreign.{Arena, MemorySegment}

given StringCallbackApi with
  extension (stringCallBack: String => Unit)
    inline def stringToStringCallback(
      using arena: Arena
    ): StringCallback =
      StringCallback(
        MlirStringCallback.allocate(
          (message: MemorySegment, userData: MemorySegment) => stringCallBack(StringRef(message).toScalaString),
          arena
        )
      )
  extension (bytesCallBack:  Array[Byte] => Unit)
    inline def bytesToStringCallback(
      using arena: Arena
    ): StringCallback =
      StringCallback(
        MlirStringCallback.allocate(
          (message: MemorySegment, userData: MemorySegment) => bytesCallBack(StringRef(message).toBytes),
          arena
        )
      )
  extension (stringCallBack: StringCallback) inline def segment: MemorySegment = stringCallBack._segment
end given

given OperationWalkCallbackApi with
  extension (operationCallBack: Operation => WalkResultEnum)
    inline def toOperationWalkCallback(
      using arena: Arena
    ): OperationWalkCallback =
      OperationWalkCallback(
        MlirOperationWalkCallback.allocate(
          (operation: MemorySegment, userData: MemorySegment) => operationCallBack(Operation(operation)).toNative,
          arena
        )
      )
  extension (operationCallBack: OperationWalkCallback) inline def segment: MemorySegment = operationCallBack._segment
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
