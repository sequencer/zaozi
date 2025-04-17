// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

import org.llvm.circt.scalalib.firrtl.capi.{
  given_FirrtlBundleFieldApi,
  given_FirrtlDirectionApi,
  given_TypeApi,
  FirrtlConvention,
  FirrtlNameKind
}
import org.llvm.circt.scalalib.firrtl.operation
import org.llvm.circt.scalalib.firrtl.operation.{
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
val constructorApi = summon[ConstructorApi]
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
    sourcecode.Name.Machine
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
      sourcecode.Name.Machine
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
    sourcecode.Name.Machine
  ): Unit =
    val op0 = summon[LayerBlockApi].op(summon[Seq[LayerTree]](layerName)._hierarchy.map(_._name), locate)
    op0.operation.appendToBlock()
    body(
      using summon[Arena],
      summon[Context],
      op0.block,
      summon[Seq[LayerTree]](layerName)._children
    )
  extension (layer: Layer)
    def toLayerTree:         LayerTree =
      new LayerTree:
        la =>
        def _name:     String         = layer.name
        def _children: Seq[LayerTree] = layer.children.map(_.toLayerTree)
      ._rebuild

  def Module[PARAM <: Parameter, I <: HWInterface[PARAM], P <: DVInterface[PARAM]](
    io:    I,
    probe: P
  )(body:  (Arena, Context, Block, Seq[LayerTree], PARAM, Interface[I], Interface[P]) ?=> Unit
  )(
    using Arena,
    Context,
    PARAM
  ): operation.Module =
    val unknownLocation  = summon[LocationApi].locationUnknownGet
    val ioNumFields      = io.toMlirType.getBundleNumFields.toInt
    val probeNumFields   = probe.toMlirType.getBundleNumFields.toInt
    val bfs              =
      Seq.tabulate(ioNumFields)(io.toMlirType.getBundleFieldByIndex) ++
        Seq.tabulate(probeNumFields)(probe.toMlirType.getBundleFieldByIndex)
    given Seq[LayerTree] = summon[PARAM].layerTrees.flatMap(_._dfs)
    val module           = summon[ModuleApi].op(
      summon[PARAM].moduleName,
      unknownLocation,
      FirrtlConvention.Scalarized,
      bfs.map(i => (i, unknownLocation)), // TODO: record location for Bundle?
      summon[Seq[LayerTree]].filter(_._children.isEmpty).map(_._hierarchy.map(_._name))
    )
    given Block          = module.block
    val ioWire           = summon[WireApi].op(
      "io",
      summon[LocationApi].locationUnknownGet,
      FirrtlNameKind.Droppable,
      io.toMlirType
    )
    ioWire.operation.appendToBlock()
    val probeWire        = summon[WireApi].op(
      "probe",
      summon[LocationApi].locationUnknownGet,
      FirrtlNameKind.Droppable,
      probe.toMlirType
    )
    probeWire.operation.appendToBlock()
    Seq
      .tabulate(ioNumFields): ioIdx =>
        (bfs(ioIdx), ioIdx)
      .foreach:
        case (bf, idx) =>
          val subRefToIOWire = summon[SubfieldApi].op(
            ioWire.result,
            idx,
            unknownLocation
          )
          subRefToIOWire.operation.appendToBlock()
          (
            if (bf.getIsFlip)
              summon[ConnectApi].op(module.getIO(idx), subRefToIOWire.result, unknownLocation)
            else
              summon[ConnectApi].op(subRefToIOWire.result, module.getIO(idx), unknownLocation)
          ).operation.appendToBlock()
    Seq
      .tabulate(probeNumFields): probeIdx =>
        (bfs(ioNumFields + probeIdx), probeIdx)
      .foreach:
        case (bf, idx) =>
          val subRefToProbeWire = summon[OpenSubfieldApi].op(
            probeWire.result,
            idx,
            unknownLocation
          )
          subRefToProbeWire.operation.appendToBlock()
          summon[RefDefineApi]
            .op(module.getIO(ioNumFields + idx), subRefToProbeWire.result, unknownLocation)
            .operation
            .appendToBlock()
    given Interface[I]   =
      new Interface[I]:
        val _tpe:       I         = io
        val _operation: Operation = ioWire.operation
    given Interface[P]   =
      new Interface[P]:
        val _tpe:       P         = probe
        val _operation: Operation = probeWire.operation
    body
    module

  def Wire[T <: Data](
    refType: T
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name.Machine
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
    sourcecode.Name.Machine
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
    sourcecode.Name.Machine
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

  def Instance[P <: Parameter, IOTpe <: HWInterface[P], ProbeTpe <: DVInterface[P]](
    ioTpe:    IOTpe,
    probeTpe: ProbeTpe
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name.Machine,
    P
    // TODO: later will also return a ClassTpe
  ): Instance[IOTpe, ProbeTpe] =
    val bfs =
      // IO
      Seq.tabulate(ioTpe.toMlirType.getBundleNumFields.toInt)(ioTpe.toMlirType.getBundleFieldByIndex) ++
        // Probe
        Seq.tabulate(probeTpe.toMlirType.getBundleNumFields.toInt)(probeTpe.toMlirType.getBundleFieldByIndex)
    // TODO: add layer symbol here? rather than from top to down searching?
    val instanceOp = summon[InstanceApi].op(
      moduleName = summon[P].moduleName,
      instanceName = valName,
      nameKind = FirrtlNameKind.Interesting,
      location = locate,
      interface = bfs
    )
    instanceOp.operation.appendToBlock()
    val ioWire     = summon[WireApi].op(
      s"${valName}_io",
      summon[LocationApi].locationUnknownGet,
      FirrtlNameKind.Droppable,
      ioTpe.toMlirType
    )
    ioWire.operation.appendToBlock()
    val probeWire  = summon[WireApi].op(
      s"${valName}_probe",
      summon[LocationApi].locationUnknownGet,
      FirrtlNameKind.Droppable,
      probeTpe.toMlirType
    )
    probeWire.operation.appendToBlock()

    bfs.zipWithIndex.foreach: (bf, idx) =>
      val flip       = bf.getIsFlip
      val instanceIO = instanceOp.operation.getResult(idx)
      val wireIO     = summon[SubfieldApi].op(
        ioWire.result,
        idx,
        locate
      )
      wireIO.operation.appendToBlock()
      val connect    =
        if (flip) summon[ConnectApi].op(wireIO.result, instanceIO, locate)
        else summon[ConnectApi].op(instanceIO, wireIO.result, locate)
      connect.operation.appendToBlock()
    new Instance[IOTpe, ProbeTpe]:
      val _ioTpe:     IOTpe          = ioTpe
      val _probeTpe:  ProbeTpe       = probeTpe
      val _operation: Operation      = instanceOp.operation
      val _ioWire:    Wire[IOTpe]    = new Wire[IOTpe]:
        private[zaozi] val _tpe       = ioTpe
        private[zaozi] val _operation = ioWire.operation
      val _probeWire: Wire[ProbeTpe] = new Wire[ProbeTpe]:
        private[zaozi] val _tpe       = probeTpe
        private[zaozi] val _operation = probeWire.operation

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
