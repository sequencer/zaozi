// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package org.llvm.circt.scalalib.smt.operation

import org.llvm.mlir.scalalib.{Block, Context, Location, LocationApi, NamedAttributeApi, Operation, OperationApi, Type, Value, Module as MlirModule, given}

import java.lang.foreign.Arena
given AddApi with
  def op(
          inputs:      Seq[Value],
          location:    Location
        )(
          using arena: Arena,
          context:     Context
        ): Add =
    Add(
      summon[OperationApi].operationCreate(
        name = "smt.add",
        location = location,
        operands = inputs,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: Add)
    def operation: Operation = ref._operation
    def result(
                using Arena
              ): Value = ref.operation.getResult(0)
end given

given ApplyFuncApi with
  def op(
          inputs:      Seq[Value],
          location:    Location
        )(
          using arena: Arena,
          context:     Context
        ): ApplyFunc =
    ApplyFunc(
      summon[OperationApi].operationCreate(
        name = "smt.add",
        location = location,
        operands = inputs,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: ApplyFunc)
    def operation: Operation = ref._operation
    def result(
                using Arena
              ): Value = ref.operation.getResult(0)
end given

