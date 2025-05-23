// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import me.jiuyang.zaozi.MonoConnect
import me.jiuyang.zaozi.reftpe.Referable
import me.jiuyang.zaozi.valuetpe.Data

import org.llvm.circt.scalalib.dialect.firrtl.operation.{ConnectApi, InvalidValueApi, given}
import org.llvm.mlir.scalalib.capi.ir.{Block, Context, given}

import java.lang.foreign.Arena

// TODO: split LHS & RHS into two different trait? this might help for Vec static accessing assignment.
given [D <: Data, SRC <: Referable[D], SINK <: Referable[D]]: MonoConnect[D, SRC, SINK] with
  extension (ref: SINK)
    def :=(
      that: SRC
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line
    ): Unit =
      summon[ConnectApi]
        .op(
          that.refer,
          ref.refer,
          locate
        )
        .operation
        .appendToBlock()
    def dontCare(
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line
    ): Unit =
      val invalidOp = summon[InvalidValueApi]
        .op(
          ref.refer.getType,
          locate
        )
      invalidOp.operation.appendToBlock()
      summon[ConnectApi]
        .op(
          invalidOp.result,
          ref.refer,
          locate
        )
        .operation
        .appendToBlock()
