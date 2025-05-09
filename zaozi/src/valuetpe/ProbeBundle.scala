// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.valuetpe

import me.jiuyang.zaozi.{LayerTree, TypeImpl}
import me.jiuyang.zaozi.magic.DynamicSubfield
import me.jiuyang.zaozi.reftpe.Ref
import org.llvm.mlir.scalalib.{Block, Context, Type, Value}

import java.lang.foreign.Arena

// The ProbeBundle is only defined at the interface of a module,
// The users should
trait ProbeBundle extends Data with DynamicSubfield:
  private[zaozi] var instantiating = true
  // valName -> BundleField
  private[zaozi] val _elements: collection.mutable.Map[String, BundleField[?]] =
    collection.mutable.Map[String, BundleField[?]]()

  def ProbeRead[T <: Data & CanProbe](
    tpe:   T,
    layer: LayerTree
  )(
    using TypeImpl,
    sourcecode.Name.Machine
  ): BundleField[RProbe[T]] =
    this.ReadProbeImpl(None, tpe, layer)

  def ProbeReadWrite[T <: Data & CanProbe](
    tpe:   T,
    layer: LayerTree
  )(
    using TypeImpl,
    sourcecode.Name.Machine
  ): BundleField[RWProbe[T]] =
    this.ReadWriteProbeImpl(None, tpe, layer)

  def getRefViaFieldValName[E <: Data](
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
  ): Ref[E] = this.getRefViaFieldValNameImpl(
    refer,
    fieldValName
  )

  def toMlirType(
    using Arena,
    Context,
    TypeImpl
  ): Type = this.toMlirTypeImpl
