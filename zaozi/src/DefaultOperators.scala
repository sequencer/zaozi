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
  AddPrimApi,
  AndPrimApi,
  AndRPrimApi,
  AsSIntPrimApi,
  AsUIntPrimApi,
  BitsPrimApi,
  CatPrimApi,
  ConnectApi,
  ConstantApi,
  DShlPrimApi,
  DShrPrimApi,
  DivPrimApi,
  EQPrimApi,
  GEQPrimApi,
  GTPrimApi,
  HeadPrimApi,
  InstanceApi,
  InvalidValueApi,
  LEQPrimApi,
  LTPrimApi,
  LayerBlockApi,
  ModuleApi,
  MulPrimApi,
  MuxPrimApi,
  NEQPrimApi,
  NodeApi,
  NotPrimApi,
  OpenSubfieldApi,
  OrPrimApi,
  OrRPrimApi,
  PadPrimApi,
  RefDefineApi,
  RefSendApi,
  RegApi,
  RegResetApi,
  RemPrimApi,
  ShlPrimApi,
  ShrPrimApi,
  SubPrimApi,
  SubfieldApi,
  TailPrimApi,
  When,
  WhenApi,
  WireApi,
  XorPrimApi,
  XorRPrimApi,
  given
}
import org.llvm.mlir.scalalib.{
  given_AttributeApi,
  given_BlockApi,
  given_IdentifierApi,
  given_LocationApi,
  given_NamedAttributeApi,
  given_OperationApi,
  given_RegionApi,
  given_TypeApi,
  given_ValueApi,
  Block,
  Context,
  Location,
  LocationApi,
  Operation,
  Type,
  Value
}

import java.lang.foreign.Arena

// When Import the default, all method in ConstructorApi should be exported
val constructorApi = summon[ConstructorApi]
export constructorApi.*

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

given [D <: Data & CanProbe, P <: RWProbe[D] | RProbe[D], SRC <: Referable[D], SINK <: Referable[P]]
  : ProbeDefine[D, P, SRC, SINK] with
  extension (ref: SINK)
    def <==(
      that: SRC
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line
    ): Unit =
      val refSendOp   = summon[RefSendApi]
        .op(
          that.refer,
          locate
        )
      val refDefineOp = summon[RefDefineApi]
        .op(
          ref.refer,
          refSendOp.result,
          locate
        )
      refSendOp.operation.appendToBlock()
      refDefineOp.operation.appendToBlock()

given TypeImpl with
  extension (ref: Interface[?])
    def operationImpl: Operation = ref._operation
    def referImpl(
      using Arena
    ): Value = ref.operation.getResult(0)
  extension (ref: Wire[?])
    def operationImpl: Operation = ref._operation
    def referImpl(
      using Arena
    ): Value = ref.operation.getResult(0)
  extension (ref: Reg[?])
    def operationImpl: Operation = ref._operation
    def referImpl(
      using Arena
    ): Value = ref.operation.getResult(0)
  extension (ref: Node[?])
    def operationImpl: Operation = ref._operation
    def referImpl(
      using Arena
    ): Value = ref.operation.getResult(0)
  extension (ref: Ref[?])
    def operationImpl: Operation = ref._operation
    def referImpl(
      using Arena
    ): Value = ref.operation.getResult(0)
  extension (ref: Const[?])
    def operationImpl: Operation = ref._operation
    def referImpl(
      using Arena
    ): Value = ref.operation.getResult(0)
  extension (ref: Instance[?, ?])
    def operationImpl:        Operation = ref._operation
    def ioImpl[T <: Data]:    Wire[T]   = ref._ioWire.asInstanceOf[Wire[T]]
    def probeImpl[T <: Data]: Wire[T]   = ref._probeWire.asInstanceOf[Wire[T]]

  extension (ref: Reset)
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type =
      val mlirType =
        if (ref._isAsync)
          summon[org.llvm.circt.scalalib.firrtl.capi.TypeApi].getAsyncReset
        else
          1.getUInt
      mlirType
  extension (ref: Clock)
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type =
      val mlirType = summon[org.llvm.circt.scalalib.firrtl.capi.TypeApi].getClock
      mlirType
  extension (ref: UInt)
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type =
      val mlirType = ref._width.getUInt
      mlirType
  extension (ref: SInt)
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type =
      val mlirType = ref._width.getSInt
      mlirType
  extension (ref: Bits)
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type =
      val mlirType = ref._width.getUInt
      mlirType
  extension (ref: Analog)
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type =
      val mlirType = ref._width.getAnalog
      mlirType
  extension (ref: Bool)
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type =
      val mlirType = 1.getUInt
      mlirType
  extension (ref: ProbeBundle)
    def elements: Seq[BundleField[?]] =
      require(!ref.instantiating)
      ref._elements.values.toSeq
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type =
      ref.instantiating = false
      val mlirType = elements
        .map(f =>
          summon[org.llvm.circt.scalalib.firrtl.capi.FirrtlBundleFieldApi]
            .createFirrtlBundleField(f._name, f._isFlip, f._tpe.toMlirType)
        )
        .getBundle
      mlirType
    def ReadProbeImpl[T <: Data & CanProbe](
      name:  Option[String],
      tpe:   T,
      layer: LayerTree
    )(
      using sourcecode.Name
    ): BundleField[RProbe[T]] =
      require(ref.instantiating)
      val bf = new BundleField[RProbe[T]]:
        val _name:   String    = name.getOrElse(valName)
        val _isFlip: Boolean   = false
        val _tpe:    RProbe[T] = new RProbe[T]:
          val _baseType: T         = tpe
          val _color:    LayerTree = layer

      ref._elements += (valName -> bf)
      bf
    def ReadWriteProbeImpl[T <: Data & CanProbe](
      name:  Option[String],
      tpe:   T,
      layer: LayerTree
    )(
      using sourcecode.Name
    ): BundleField[RWProbe[T]] =
      require(ref.instantiating)
      val bf = new BundleField[RWProbe[T]]:
        val _name:   String     = name.getOrElse(valName)
        val _isFlip: Boolean    = false
        val _tpe:    RWProbe[T] = new RWProbe[T]:
          val _baseType: T         = tpe
          val _color:    LayerTree = layer

      ref._elements += (valName -> bf)
      bf

  extension (ref: Bundle)
    def elements: Seq[BundleField[?]] =
      require(!ref.instantiating)
      ref._elements.values.toSeq
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type =
      ref.instantiating = false
      val mlirType = elements
        .map(f =>
          summon[org.llvm.circt.scalalib.firrtl.capi.FirrtlBundleFieldApi]
            .createFirrtlBundleField(f._name, f._isFlip, f._tpe.toMlirType)
        )
        .getBundle
      mlirType
    def FlippedImpl[T <: Data](
      name: Option[String],
      tpe:  T
    )(
      using sourcecode.Name
    ): BundleField[T] =
      require(ref.instantiating)
      val bf = new BundleField[T]:
        val _name:   String  = name.getOrElse(valName)
        val _isFlip: Boolean = true
        val _tpe:    T       = tpe
      ref._elements += (valName -> bf)
      bf

    def AlignedImpl[T <: Data](
      name: Option[String],
      tpe:  T
    )(
      using sourcecode.Name
    ): BundleField[T] =
      require(ref.instantiating)
      val bf = new BundleField[T]:
        val _name:   String  = name.getOrElse(valName)
        val _isFlip: Boolean = false
        val _tpe:    T       = tpe
      ref._elements += (valName -> bf)
      bf
  extension (ref: RProbe[?])
    def toMlirTypeImpl(
      using Arena,
      Context,
      TypeImpl
    ): Type =
      ref._baseType.toMlirType.getRef(false, ref._color._hierarchy.map(_._name))

  extension (ref: RWProbe[?])
    def toMlirTypeImpl(
      using Arena,
      Context,
      TypeImpl
    ): Type =
      ref._baseType.toMlirType.getRef(true, ref._color._hierarchy.map(_._name))

  extension (ref: Vec[?])
    def elementType: Data = ref._elementType
    def count:       Int  = ref._count
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type =
      val mlirType = elementType.toMlirType.getVector(count)
      mlirType
  extension (ref: ProbeBundle)
    def getRefViaFieldValNameImpl[E <: Data](
      refer:        Value,
      fieldValName: String
    )(
      using Arena,
      Block,
      Context,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    )(
      using TypeImpl
    ): Ref[E] =
      def valNameToRefName(valName: String):        String =
        ref._elements
          .getOrElse(valName, throw new Exception(s"$valName not found in ${ref._elements.keys}"))
          ._name
      def valNameToTpe[T <: Data](valName: String): T      =
        ref._elements(valName)._tpe.asInstanceOf[T]
      val openSubfieldOp = summon[OpenSubfieldApi]
        .op(
          input = refer,
          fieldIndex = ref.toMlirType.getBundleFieldIndex(valNameToRefName(fieldValName)),
          location = locate
        )
      openSubfieldOp.operation.appendToBlock()
      new Ref[E]:
        val _tpe:       E         = valNameToTpe(fieldValName)
        val _operation: Operation = openSubfieldOp.operation
  extension (ref: Bundle)
    def getRefViaFieldValNameImpl[E <: Data](
      refer:        Value,
      fieldValName: String
    )(
      using Arena,
      Block,
      Context,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    )(
      using TypeImpl
    ): Ref[E] =
      def valNameToRefName(valName: String):        String =
        ref._elements
          .getOrElse(valName, throw new Exception(s"$valName not found in ${ref._elements.keys}"))
          ._name
      def valNameToTpe[T <: Data](valName: String): T      =
        ref._elements(valName)._tpe.asInstanceOf[T]
      val subfieldOp = summon[SubfieldApi]
        .op(
          input = refer,
          fieldIndex = ref.toMlirType.getBundleFieldIndex(valNameToRefName(fieldValName)),
          location = locate
        )
      subfieldOp.operation.appendToBlock()
      new Ref[E]:
        val _tpe:       E         = valNameToTpe(fieldValName)
        val _operation: Operation = subfieldOp.operation
end given

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

  def when[COND <: Referable[Bool]](
    cond: COND
  )(body: (Arena, Context, Block) ?=> Unit
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
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
      sourcecode.Name
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
    sourcecode.Name
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
    parameter: PARAM,
    io:        I,
    probe:     P
  )(body:      (Arena, Context, Block, Seq[Layer], PARAM, Interface[I], Interface[P]) ?=> Unit
  )(
    using Arena,
    Context
  ): operation.Module =
    val unknownLocation  = summon[LocationApi].locationUnknownGet
    val ioNumFields      = io.toMlirType.getBundleNumFields.toInt
    val probeNumFields   = probe.toMlirType.getBundleNumFields.toInt
    val bfs              =
      Seq.tabulate(ioNumFields)(io.toMlirType.getBundleFieldByIndex) ++
        Seq.tabulate(probeNumFields)(probe.toMlirType.getBundleFieldByIndex)
    given Seq[LayerTree] = summon[PARAM].layerTrees.flatMap(_._dfs)
    val module           = summon[ModuleApi].op(
      parameter.moduleName,
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
            if (bf.getIsFlip())
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
    given PARAM          = parameter
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
    sourcecode.Name
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
    sourcecode.Name
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
    sourcecode.Name
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
    parameter: P,
    ioTpe:     IOTpe,
    probeTpe:  ProbeTpe
  )(
    using Arena,
    Context,
    Block,
    Ref[Clock],
    Ref[Reset],
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
    // TODO: later will also return a ClassTpe
  ): Instance[IOTpe, ProbeTpe] =
    val bfs =
      // IO
      Seq.tabulate(ioTpe.toMlirType.getBundleNumFields.toInt)(ioTpe.toMlirType.getBundleFieldByIndex) ++
        // Probe
        Seq.tabulate(probeTpe.toMlirType.getBundleNumFields.toInt)(probeTpe.toMlirType.getBundleFieldByIndex)
    // TODO: add layer symbol here? rather than from top to down searching?
    val instanceOp = summon[InstanceApi].op(
      moduleName = parameter.moduleName,
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
      val flip       = bf.getIsFlip()
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

given [R <: Referable[Bits]]: BitsApi[R] with
  extension (ref: R)
    def asSInt(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
end given

given [R <: Referable[UInt]]: UIntApi[R] with
  extension (ref: R)
    def asBits(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[Bits] =
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = ref.refer
      )
      nodeOp.operation.appendToBlock()
      new Node[Bits]:
        val _tpe:       Bits      = new Bits:
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation

    def +(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[UInt] =
      val op0    = summon[AddPrimApi].op(ref.refer, that.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[UInt]:
        val _tpe:       UInt      = new UInt:
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
      sourcecode.Name
    ): Node[UInt] =
      val op0    = summon[SubPrimApi].op(ref.refer, that.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[UInt]:
        val _tpe:       UInt      = new UInt:
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
      sourcecode.Name
    ): Node[UInt] =
      val op0    = summon[MulPrimApi].op(ref.refer, that.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[UInt]:
        val _tpe:       UInt      = new UInt:
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
      sourcecode.Name
    ): Node[UInt] =
      val op0    = summon[DivPrimApi].op(ref.refer, that.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[UInt]:
        val _tpe:       UInt      = new UInt:
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
      sourcecode.Name
    ): Node[UInt] =
      val op0    = summon[RemPrimApi].op(ref.refer, that.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[UInt]:
        val _tpe:       UInt      = new UInt:
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
    ): Node[UInt] =
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
      new Node[UInt]:
        val _tpe:       UInt      = new UInt:
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
      sourcecode.Name
    ): Node[UInt] =
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
      new Node[UInt]:
        val _tpe:       UInt      = new UInt:
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation
end given

given [R <: Referable[SInt]]: SIntApi[R] with
  extension (ref: R)
    def asBits(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
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

given [R <: Referable[Bool]]: BoolApi[R] with
  extension (ref: R)
    def unary_!(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[Bool] =
      val op0    = summon[NotPrimApi].op(ref.refer, locate)
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

    def asBits(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[Bits] =
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = ref.refer
      )
      nodeOp.operation.appendToBlock()
      new Node[Bits]:
        val _tpe:       Bits      = new Object with Bits:
          private[zaozi] val _width = nodeOp.operation.getResult(0).getType.getBitWidth(true).toInt
        val _operation: Operation = nodeOp.operation

    def ===(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
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
      sourcecode.Name
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
      sourcecode.Name
    ): Node[Bool] =
      val op0    = summon[AndPrimApi].op(ref.refer, that.refer, locate)
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

    def |(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[Bool] =
      val op0    = summon[OrPrimApi].op(ref.refer, that.refer, locate)
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

    def ^(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[Bool] =
      val op0    = summon[XorPrimApi].op(ref.refer, that.refer, locate)
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

    def ?[Ret <: Data](
      con: Referable[Ret],
      alt: Referable[Ret]
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[Ret] =
      val op0    = summon[MuxPrimApi].op(ref.refer, con.refer, alt.refer, locate)
      op0.operation.appendToBlock()
      val nodeOp = summon[NodeApi].op(
        name = valName,
        location = locate,
        nameKind = FirrtlNameKind.Interesting,
        input = op0.result
      )
      nodeOp.operation.appendToBlock()
      new Node[Ret]:
        val _tpe:       Ret       = con._tpe
        val _operation: Operation = nodeOp.operation
end given

private inline def locate(
  using Arena,
  Context,
  sourcecode.File,
  sourcecode.Line
): Location =
  summon[LocationApi].locationFileLineColGet(
    summon[sourcecode.File].value,
    summon[sourcecode.Line].value,
    0
  )

private inline def valName(
  using sourcecode.Name
): String = summon[sourcecode.Name].value
