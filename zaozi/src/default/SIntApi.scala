// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import me.jiuyang.zaozi.SIntApi
import me.jiuyang.zaozi.InstanceContext
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

import org.llvm.circt.scalalib.capi.dialect.firrtl.{given_FirrtlBundleFieldApi, given_TypeApi, FirrtlNameKind}
import org.llvm.circt.scalalib.dialect.firrtl.operation.{
  AddPrimApi,
  AsUIntPrimApi,
  DShlPrimApi,
  DShrPrimApi,
  DivPrimApi,
  EQPrimApi,
  GEQPrimApi,
  GTPrimApi,
  LEQPrimApi,
  LTPrimApi,
  MulPrimApi,
  NEQPrimApi,
  NodeApi,
  RemPrimApi,
  ShlPrimApi,
  ShrPrimApi,
  SubPrimApi,
  given
}
import org.llvm.mlir.scalalib.capi.ir.{Block, Context, LocationApi, Operation, given}

import java.lang.foreign.Arena

given [R <: Referable[SInt]]: SIntApi[R] with
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
      val op0    = summon[AsUIntPrimApi].op(ref.refer, locate)
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
    def +(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[SInt] =
      val op0    = summon[AddPrimApi].op(ref.refer, that.refer, locate)
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
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation

    def -(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[SInt] =
      val op0    = summon[SubPrimApi].op(ref.refer, that.refer, locate)
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
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation

    def *(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[SInt] =
      val op0    = summon[MulPrimApi].op(ref.refer, that.refer, locate)
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
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation

    def /(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[SInt] =
      val op0    = summon[DivPrimApi].op(ref.refer, that.refer, locate)
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
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation

    def %(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[SInt] =
      val op0    = summon[RemPrimApi].op(ref.refer, that.refer, locate)
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
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation

    def <(
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
      val op0    = summon[LTPrimApi].op(ref.refer, that.refer, locate)
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

    def <=(
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
      val op0    = summon[LEQPrimApi].op(ref.refer, that.refer, locate)
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

    def >(
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
      val op0    = summon[GTPrimApi].op(ref.refer, that.refer, locate)
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

    def >=(
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
      val op0    = summon[GEQPrimApi].op(ref.refer, that.refer, locate)
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
    ): Node[SInt] =
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
      new Node[SInt]:
        val _tpe:       SInt      = new SInt:
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
    ): Node[SInt] =
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
      new Node[SInt]:
        val _tpe:       SInt      = new SInt:
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation
end given
