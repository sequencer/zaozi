// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.ir

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{
  mlirOperationStateAddAttributes,
  mlirOperationStateAddOperands,
  mlirOperationStateAddOwnedRegions,
  mlirOperationStateAddResults,
  mlirOperationStateAddSuccessors,
  mlirOperationStateEnableResultTypeInference,
  mlirOperationStateGet
}
import org.llvm.mlir.scalalib.capi.support.{*, given}

import java.lang.foreign.{Arena, MemorySegment}

given OperationStateApi with
  inline def operationStateGet(
    name:        String,
    loc:         Location
  )(
    using arena: Arena
  ): OperationState =
    OperationState(mlirOperationStateGet(arena, name.toStringRef.segment, loc.segment))

  extension (operationState: OperationState)
    inline def addResults(
      results:     Seq[Type]
    )(
      using arena: Arena
    ): Unit =
      mlirOperationStateAddResults(operationState.segment, results.size, results.toMlirArray)
    inline def addOperands(
      operands:    Seq[Value]
    )(
      using arena: Arena
    ): Unit =
      mlirOperationStateAddOperands(operationState.segment, operands.size, operands.toMlirArray)
    inline def addOwnedRegions(
      regions:     Seq[Region]
    )(
      using arena: Arena
    ): Unit =
      mlirOperationStateAddOwnedRegions(operationState.segment, regions.size, regions.toMlirArray)
    inline def addSuccessors(
      blocks:      Seq[Block]
    )(
      using arena: Arena
    ): Unit =
      mlirOperationStateAddSuccessors(operationState.segment, blocks.size, blocks.toMlirArray)
    inline def addAttributes(
      attrs:       Seq[NamedAttribute]
    )(
      using arena: Arena
    ): Unit =
      mlirOperationStateAddAttributes(operationState.segment, attrs.size, attrs.toMlirArray)
    inline def enableResultTypeInference(): Unit          =
      mlirOperationStateEnableResultTypeInference(operationState.segment)
    inline def segment:                     MemorySegment = operationState._segment
    inline def sizeOf:                      Int           = MlirOperationState.sizeof().toInt
end given
