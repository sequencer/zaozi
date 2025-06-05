// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.valuetpe

import me.jiuyang.zaozi.TypeImpl
import me.jiuyang.zaozi.magic.DynamicSubfield
import me.jiuyang.zaozi.reftpe.Ref
import org.llvm.mlir.scalalib.capi.ir.{Block, Context, Type, Value}

import java.lang.foreign.Arena

trait Bundle extends Data with DynamicSubfield:
  private[zaozi] var instantiating = true

  private[zaozi] val _elements = collection.mutable.Buffer.empty[BundleField[?]]

  def Flipped[T <: Data](
    tpe: T
  )(
    using TypeImpl,
    sourcecode.Name.Machine
  ): BundleField[T] = this.FlippedImpl(tpe)

  def Aligned[T <: Data](
    tpe: T
  )(
    using TypeImpl,
    sourcecode.Name.Machine
  ): BundleField[T] = this.AlignedImpl(tpe)

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

  def getOptionRefViaFieldValName[E <: Data](
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
  ): Option[Ref[E]] = this.getOptionRefViaFieldValNameImpl(
    refer,
    fieldValName
  )

  def toMlirType(
    using Arena,
    Context,
    TypeImpl
  ): Type = this.toMlirTypeImpl

trait BundleField[T <: Data]:
  private[zaozi] val _name:   String
  private[zaozi] val _isFlip: Boolean
  private[zaozi] val _tpe:    T
