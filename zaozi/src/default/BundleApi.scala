// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.magic.UntypedDynamicSubfield
import me.jiuyang.zaozi.reftpe.Node
import me.jiuyang.zaozi.reftpe.{Ref, Referable}
import me.jiuyang.zaozi.valuetpe.Bits
import me.jiuyang.zaozi.valuetpe.Bundle
import me.jiuyang.zaozi.valuetpe.ProbeBundle
import me.jiuyang.zaozi.valuetpe.{Data, ProbeRecord, Record}
import org.llvm.circt.scalalib.capi.dialect.firrtl.{*, given}
import org.llvm.circt.scalalib.dialect.firrtl.operation.{given_BitCastApi, BitCastApi}
import org.llvm.circt.scalalib.dialect.firrtl.operation.{given_WireApi, WireApi}
import org.llvm.mlir.scalalib.capi.ir.{*, given}

import java.lang.foreign.Arena

given [T <: Bundle | ProbeBundle, R <: Referable[T]]: BundleApi[T, R] with
  extension (ref: R)
    def asBits(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] =
      val bitcastOp = summon[BitCastApi].op(
        input = ref.refer,
        tpe = Bits(ref.refer.getType.getBitWidth(true).toInt.W).toMlirType,
        location = locate
      )
      bitcastOp.operation.appendToBlock()
      new Node[Bits]:
        val _tpe:       Bits      = new Bits:
          private[zaozi] val _width = bitcastOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = bitcastOp.operation
end given
