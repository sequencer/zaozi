// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

import org.llvm.circt.scalalib.firrtl.capi.given
import org.llvm.circt.scalalib.firrtl.operation.{OpenSubfieldApi, SubfieldApi, given}
import org.llvm.mlir.scalalib.{Block, Context, LocationApi, Operation, Type, Value, given}

import java.lang.foreign.Arena

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
      using sourcecode.Name.Machine
    ): BundleField[RProbe[T]] =
      require(ref.instantiating)
      val bf = new BundleField[RProbe[T]]:
        val _name:   String    = name.getOrElse(bundleFieldName)
        val _isFlip: Boolean   = false
        val _tpe:    RProbe[T] = new RProbe[T]:
          val _baseType: T         = tpe
          val _color:    LayerTree = layer

      ref._elements += (bundleFieldName -> bf)
      bf
    def ReadWriteProbeImpl[T <: Data & CanProbe](
      name:  Option[String],
      tpe:   T,
      layer: LayerTree
    )(
      using sourcecode.Name.Machine
    ): BundleField[RWProbe[T]] =
      require(ref.instantiating)
      val bf = new BundleField[RWProbe[T]]:
        val _name:   String     = name.getOrElse(bundleFieldName)
        val _isFlip: Boolean    = false
        val _tpe:    RWProbe[T] = new RWProbe[T]:
          val _baseType: T         = tpe
          val _color:    LayerTree = layer

      ref._elements += (bundleFieldName -> bf)
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
      using sourcecode.Name.Machine
    ): BundleField[T] =
      require(ref.instantiating)
      val bf = new BundleField[T]:
        val _name:   String  = name.getOrElse(bundleFieldName)
        val _isFlip: Boolean = true
        val _tpe:    T       = tpe
      ref._elements += (bundleFieldName -> bf)
      bf

    def AlignedImpl[T <: Data](
      name: Option[String],
      tpe:  T
    )(
      using sourcecode.Name.Machine
    ): BundleField[T] =
      require(ref.instantiating)
      val bf = new BundleField[T]:
        val _name:   String  = name.getOrElse(bundleFieldName)
        val _isFlip: Boolean = false
        val _tpe:    T       = tpe
      ref._elements += (bundleFieldName -> bf)
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
      sourcecode.Name.Machine
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
      sourcecode.Name.Machine
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
