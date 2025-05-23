// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.ir

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{
  mlirBlockAddArgument,
  mlirBlockAppendOwnedOperation,
  mlirBlockArgumentGetOwner,
  mlirBlockCreate,
  mlirBlockDestroy,
  mlirBlockDetach,
  mlirBlockEraseArgument,
  mlirBlockGetArgument,
  mlirBlockGetFirstOperation,
  mlirBlockGetNextInRegion,
  mlirBlockGetParentOperation,
  mlirBlockGetTerminator,
  mlirBlockInsertArgument,
  mlirBlockInsertOwnedOperation,
  mlirBlockInsertOwnedOperationAfter,
  mlirBlockInsertOwnedOperationBefore,
  mlirBlockPrint
}
import org.llvm.mlir.scalalib.capi.support.{*, given}

import java.lang.foreign.{Arena, MemorySegment}

given BlockApi with
  inline def blockCreate(
    args:        Seq[Type],
    locs:        Seq[Location]
  )(
    using arena: Arena
  ): Block =
    Block(mlirBlockCreate(arena, args.length, args.toMlirArray, locs.toMlirArray))

  extension (block: Block)
    inline def getParentOperation(
      using arena: Arena
    ): Operation = Operation(mlirBlockGetParentOperation(arena, block.segment))
    inline def getNextInRegion(
      using arena: Arena
    ): Block = Block(mlirBlockGetNextInRegion(arena, block.segment))
    inline def getFirstOperation(
      using arena: Arena
    ): Operation = Operation(mlirBlockGetFirstOperation(arena, block.segment))
    inline def getTerminator(
      using arena: Arena
    ): Operation = Operation(mlirBlockGetTerminator(arena, block.segment))
    inline def addArgument(
      tpe:         Type,
      loc:         Location
    )(
      using arena: Arena
    ): Operation = Operation(mlirBlockAddArgument(arena, block.segment, tpe.segment, loc.segment))
    inline def insertArgument(
      pos:         Int,
      tpe:         Type,
      loc:         Location
    )(
      using arena: Arena
    ): Operation = Operation(mlirBlockInsertArgument(arena, block.segment, pos, tpe.segment, loc.segment))
    inline def getArgument(
      pos:         Long
    )(
      using arena: Arena
    ): Value = Value(mlirBlockGetArgument(arena, block.segment, pos))
    inline def argumentGetOwner(
      using arena: Arena
    ): Block = Block(mlirBlockArgumentGetOwner(arena, block.segment))
    inline def destroy():                                                              Unit = mlirBlockDestroy(block.segment)
    inline def detach():                                                               Unit = mlirBlockDetach(block.segment)
    inline def appendOwnedOperation(operation: Operation):                             Unit =
      mlirBlockAppendOwnedOperation(block.segment, operation.segment)
    inline def insertOwnedOperation(pos: Long, operation: Operation):                  Unit =
      mlirBlockInsertOwnedOperation(block.segment, pos, operation.segment)
    inline def insertOwnedOperationAfter(reference: Operation, operation: Operation):  Unit =
      mlirBlockInsertOwnedOperationAfter(block.segment, reference.segment, operation.segment)
    inline def insertOwnedOperationBefore(reference: Operation, operation: Operation): Unit =
      mlirBlockInsertOwnedOperationBefore(block.segment, reference.segment, operation.segment)
    inline def eraseArgument(index: Int): Unit = mlirBlockEraseArgument(block.segment, index)
    inline def print(
      callBack:    String => Unit
    )(
      using arena: Arena
    ): Unit = mlirBlockPrint(block.segment, callBack.stringToStringCallback.segment, MemorySegment.NULL)
    inline def segment: MemorySegment = block._segment
    inline def sizeOf: Int = MlirBlock.sizeof().toInt

end given
