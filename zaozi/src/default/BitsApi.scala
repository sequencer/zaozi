// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import me.jiuyang.zaozi.BitsApi
import me.jiuyang.zaozi.InstanceContext
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

import org.llvm.circt.scalalib.capi.dialect.firrtl.{given_FirrtlBundleFieldApi, given_TypeApi, FirrtlNameKind}
import org.llvm.circt.scalalib.dialect.firrtl.operation.{
  AndPrimApi,
  AndRPrimApi,
  AsSIntPrimApi,
  BitsPrimApi,
  CatPrimApi,
  DShlPrimApi,
  DShrPrimApi,
  EQPrimApi,
  HeadPrimApi,
  NEQPrimApi,
  NodeApi,
  NotPrimApi,
  OrPrimApi,
  OrRPrimApi,
  PadPrimApi,
  ShlPrimApi,
  ShrPrimApi,
  TailPrimApi,
  XorPrimApi,
  XorRPrimApi,
  given
}
import org.llvm.mlir.scalalib.capi.ir.{Block, Context, LocationApi, Operation, given}

import java.lang.foreign.Arena

given [R <: Referable[Bits]]: BitsApi[R] with
  extension (ref: R)
    def asSInt(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[SInt] =
      val op0    = summon[AsSIntPrimApi].op(ref.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[SInt]:
        val _tpe:       SInt      = new SInt:
          private[zaozi] val _width = op0.result.getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation
    def asUInt(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[UInt] =
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = ref.refer
      )
      nodeOp.operation.appendToBlock()
      new Node[UInt]:
        val _tpe:       UInt      = new UInt:
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation

    def unary_~(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] =
      val op0    = summon[NotPrimApi].op(ref.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bits]:
        val _tpe:       Bits      = new Bits:
          private[zaozi] val _width = op0.result.getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation

    def andR(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bool] =
      val op0    = summon[AndRPrimApi].op(ref.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bool]:
        val _tpe:       Bool      = new Object with Bool
        val _operation: Operation = nodeOp.operation

    def orR(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bool] =
      val op0    = summon[OrRPrimApi].op(ref.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bool]:
        val _tpe:       Bool      = new Object with Bool
        val _operation: Operation = nodeOp.operation

    def xorR(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bool] =
      val op0    = summon[XorRPrimApi].op(ref.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bool]:
        val _tpe:       Bool      = new Object with Bool
        val _operation: Operation = nodeOp.operation

    def ===(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bool] =
      val op0    = summon[EQPrimApi].op(ref.refer, that.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bool]:
        val _tpe:       Bool      = new Object with Bool
        val _operation: Operation = nodeOp.operation
    def =/=(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bool] =
      val op0    = summon[NEQPrimApi].op(ref.refer, that.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bool]:
        val _tpe:       Bool      = new Object with Bool
        val _operation: Operation = nodeOp.operation
    def &(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] =
      val op0    = summon[AndPrimApi].op(ref.refer, that.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bits]:
        val _tpe:       Bits      = new Bits:
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation
    def |(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] =
      val op0    = summon[OrPrimApi].op(ref.refer, that.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bits]:
        val _tpe:       Bits      = new Bits:
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation

    def ^(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] =
      val op0    = summon[XorPrimApi].op(ref.refer, that.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bits]:
        val _tpe:       Bits      = new Bits:
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation

    def ##(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] =
      val op0    = summon[CatPrimApi].op(ref.refer, that.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bits]:
        val _tpe:       Bits      = new Bits:
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation
    def <<(
      that: Int | Referable[UInt]
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] =
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = that match
          case that: Int             =>
            val op0 = summon[ShlPrimApi].op(ref.refer, that, locate)
            op0.operation.appendToBlock()
            op0.result
          case that: Referable[UInt] =>
            val op0 = summon[DShlPrimApi].op(ref.refer, that.refer, locate)
            op0.operation.appendToBlock()
            op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bits]:
        val _tpe:       Bits      = new Bits:
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation
    def >>(
      that: Int | Referable[UInt]
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] =
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = that match
          case that: Int             =>
            val op0 = summon[ShrPrimApi].op(ref.refer, that, locate)
            op0.operation.appendToBlock()
            op0.result
          case that: Referable[UInt] =>
            val op0 = summon[DShrPrimApi].op(ref.refer, that.refer, locate)
            op0.operation.appendToBlock()
            op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bits]:
        val _tpe:       Bits      = new Bits:
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation

    def head(
      that: Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] =
      val op0    = summon[HeadPrimApi].op(ref.refer, that, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bits]:
        val _tpe:       Bits      = new Bits:
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation
    def tail(
      that: Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] =
      val op0    = summon[TailPrimApi].op(ref.refer, that, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bits]:
        val _tpe:       Bits      = new Bits:
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation
    def pad(
      that: Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] =
      val op0    = summon[PadPrimApi].op(ref.refer, that, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bits]:
        val _tpe:       Bits      = new Bits:
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation
    def bits(
      hi: Int,
      lo: Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] =
      val op0    = summon[BitsPrimApi].op(ref.refer, hi, lo, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Bits]:
        val _tpe:       Bits      = new Bits:
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation

    def bit(
      idx: Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] = bits(idx, idx)

    // sugars
    def apply(
      hi: Int,
      lo: Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] = bits(hi, lo)

    def apply(
      idx: Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] = bit(idx)
end given
