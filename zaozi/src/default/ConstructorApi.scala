// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

import org.llvm.circt.scalalib.capi.dialect.firrtl.{
  given_FirrtlBundleFieldApi,
  given_FirrtlDirectionApi,
  given_TypeApi,
  FirrtlConvention,
  FirrtlNameKind
}
import org.llvm.circt.scalalib.dialect.firrtl.operation
import org.llvm.circt.scalalib.dialect.firrtl.operation.{
  ConnectApi,
  ConstantApi,
  InstanceApi,
  LayerBlockApi,
  ModuleApi,
  OpenSubfieldApi,
  RefDefineApi,
  RegApi,
  RegResetApi,
  SubfieldApi,
  When,
  WhenApi,
  WireApi,
  given
}
import org.llvm.mlir.scalalib.{Block, Context, LocationApi, Operation, given}

import java.lang.foreign.Arena

// When Import the default, all method in ConstructorApi should be exported
export given_ConstructorApi.*

given ConstructorApi with
  def Clock(): Clock = new Object with Clock
  def Reset(): Reset = new Reset:
    val _isAsync: Boolean = false

  def AsyncReset(): Reset = new Reset:
    val _isAsync: Boolean = true

  def UInt(width: Width): UInt = new UInt:
    private[zaozi] val _width: Int = width._width

  def Bits(width: Width): Bits = new Bits:
    private[zaozi] val _width: Int = width._width

  def SInt(width: Width): SInt = new SInt:
    private[zaozi] val _width: Int = width._width

  def Bool(): Bool = new Object with Bool

  def Vec[T <: Data](count: Int, tpe: T): Vec[T] =
    new Vec[T]:
      private[zaozi] val _elementType = tpe
      private[zaozi] val _count       = count

  def when[COND <: Referable[Bool]](
    cond: COND
  )(body: (Arena, Context, Block) ?=> Unit
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name.Machine,
    InstanceContext
  ): When =
    val op0 = summon[WhenApi].op(cond.refer, locate)
    op0.operation.appendToBlock()
    body(
      using summon[Arena],
      summon[Context],
      op0.condBlock
    )
    op0

  extension (when: When)
    def otherwise(
      body: (Arena, Context, Block) ?=> Unit
    )(
      using Arena,
      Context,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Unit =
      given Block = when.elseBlock
      body

  extension (layer: LayerTree)
    def apply(name: String): LayerTree =
      layer._children(name)

  extension (layers: Seq[LayerTree])
    def apply(name: String): LayerTree =
      layers
        .find(_._name == name)
        .getOrElse(
          throw new Exception(s"No valid layer named: \"${name}\" found in ${layers.map(_._name).mkString(",")}")
        )

  def layer(
    layerName: String
  )(body:      (Arena, Context, Block, Seq[LayerTree]) ?=> Unit
  )(
    using Arena,
    Context,
    Block,
    Seq[LayerTree],
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name.Machine,
    InstanceContext
  ): Unit =
    val op0 = summon[LayerBlockApi].op(summon[Seq[LayerTree]](layerName)._hierarchy.map(_._name), locate)
    op0.operation.appendToBlock()
    body(
      using summon[Arena],
      summon[Context],
      op0.block,
      summon[Seq[LayerTree]](layerName)._children
    )

  def Wire[T <: Data](
    refType: T
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name.Machine,
    InstanceContext
  ): Wire[T] =
    val wireOp = summon[WireApi].op(
      name = valName,
      location = locate,
      nameKind = FirrtlNameKind.Interesting,
      tpe = refType.toMlirType
    )
    wireOp.operation.appendToBlock()
    new Wire[T]:
      val _tpe:       T         = refType
      val _operation: Operation = wireOp.operation

  def Reg[T <: Data](
    refType: T
  )(
    using Arena,
    Context,
    Block,
    Ref[Clock],
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name.Machine,
    InstanceContext
  ): Reg[T] =
    val regOp = summon[RegApi].op(
      name = valName,
      location = locate,
      nameKind = FirrtlNameKind.Interesting,
      tpe = refType.toMlirType,
      clock = summon[Ref[Clock]].refer
    )
    regOp.operation.appendToBlock()
    new Reg[T]:
      val _tpe:       T         = refType
      val _operation: Operation = regOp.operation

  def RegInit[T <: Data](
    input: Const[T]
  )(
    using Arena,
    Context,
    Block,
    Ref[Clock],
    Ref[Reset],
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name.Machine,
    InstanceContext
  ): Reg[T] =
    val regResetOp = summon[RegResetApi].op(
      name = valName,
      location = locate,
      nameKind = FirrtlNameKind.Interesting,
      tpe = input._tpe.toMlirType,
      clock = summon[Ref[Clock]].refer,
      reset = summon[Ref[Reset]].refer,
      resetValue = input.refer
    )
    regResetOp.operation.appendToBlock()
    new Reg[T]:
      val _tpe:       T         = input._tpe
      val _operation: Operation = regResetOp.operation

  extension (bigInt: BigInt)
    def U(
      width: Width
    )(
      using Arena,
      Context,
      Block
    ): Const[UInt] =
      val constOp = summon[ConstantApi].op(
        input = bigInt,
        width = width._width,
        signed = false,
        location = locate
      )
      constOp.operation.appendToBlock()
      new Const[UInt]:
        val _tpe:       UInt      = new UInt:
          private[zaozi] val _width = constOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = constOp.operation
    def U(
      using Arena,
      Context,
      Block
    ): Const[UInt] = bigInt.U(scala.math.max(1, bigInt.bitLength).W)
    def B(
      width: Width
    )(
      using Arena,
      Context,
      Block
    ): Const[Bits] =
      val constOp = summon[ConstantApi].op(
        input = bigInt,
        width = width._width,
        signed = false,
        location = locate
      )
      constOp.operation.appendToBlock()
      new Const[Bits]:
        val _tpe:       Bits      = new Bits:
          private[zaozi] val _width = constOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = constOp.operation
    def B(
      using Arena,
      Context,
      Block
    ): Const[Bits] = bigInt.B(scala.math.max(1, bigInt.bitLength).W)
    def S(
      width: Width
    )(
      using Arena,
      Context,
      Block
    ): Const[SInt] =
      val constOp = summon[ConstantApi].op(
        input = bigInt,
        width = width._width,
        signed = true,
        location = locate
      )
      constOp.operation.appendToBlock()
      new Const[SInt]:
        val _tpe:       SInt      = new SInt:
          private[zaozi] val _width = constOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = constOp.operation
    def S(
      using Arena,
      Context,
      Block
    ): Const[SInt] =
      // MSB for sign
      bigInt.S((bigInt.bitLength + 1).W)
    def W: Width = new Width:
      val _width: Int = bigInt.toInt
  extension (bool:   Boolean)
    def B(
      using Arena,
      Context,
      Block
    ): Const[Bool] =
      val constOp = summon[ConstantApi].op(
        input = if (bool) 1 else 0,
        width = 1,
        signed = false,
        location = locate
      )
      constOp.operation.appendToBlock()
      new Const[Bool]:
        val _tpe:       Bool      = new Object with Bool
        val _operation: Operation = constOp.operation
end given
