// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import me.jiuyang.zaozi.{InstanceContext, ResetApi}

import org.llvm.circt.scalalib.capi.dialect.firrtl.{given_TypeApi, FirrtlNameKind}
import org.llvm.circt.scalalib.dialect.firrtl.operation.{NodeApi, given}
import org.llvm.mlir.scalalib.capi.ir.{Block, Context, LocationApi, Operation, given}

import java.lang.foreign.Arena
import org.llvm.circt.scalalib.dialect.firrtl.operation.AsUIntPrimApi

given [R <: Referable[Reset]]: ResetApi[R] with
  extension (ref: R)
    def asBool(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bool] =
      val asUIntOp = summon[AsUIntPrimApi].op(ref.refer, locate)
      asUIntOp.operation.appendToBlock()
      val nodeOp   = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = asUIntOp.operation.getResult(0)
      )
      nodeOp.operation.appendToBlock()
      new Node[Bool]:
        val _tpe:       Bool      = new Object with Bool
        val _operation: Operation = nodeOp.operation
end given
