// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import me.jiuyang.zaozi.VecApi
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

import org.llvm.circt.scalalib.firrtl.capi.{given_FirrtlBundleFieldApi, given_TypeApi, FirrtlNameKind}
import org.llvm.circt.scalalib.firrtl.operation.{NodeApi, SubaccessApi, SubindexApi, given}
import org.llvm.mlir.scalalib.{Block, Context, LocationApi, Operation, given}

import java.lang.foreign.Arena

given [E <: Data, V <: Vec[E], R <: Referable[V]]: VecApi[E, V, R] with
  extension (ref: R)
    def bit(
      idx: Referable[UInt] | Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine
    ): Node[E] =
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = idx match
          case that: Referable[UInt] =>
            val op0 = summon[SubaccessApi].op(ref.refer, that.refer, locate)
            op0.operation.appendToBlock()
            op0.result
          case that: Int             =>
            val op0 = summon[SubindexApi].op(ref.refer, that, locate)
            op0.operation.appendToBlock()
            op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[E]:
        val _tpe:       E         = ref._tpe._elementType
        val _operation: Operation = nodeOp.operation

    // sugars
    def apply(
      idx: Referable[UInt] | Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine
    ): Node[E] = bit(idx)

end given
