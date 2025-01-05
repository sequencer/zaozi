// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.valuetpe

import me.jiuyang.zaozi.TypeImpl
import me.jiuyang.zaozi.magic.DynamicSubfield
import me.jiuyang.zaozi.reftpe.Ref
import org.llvm.mlir.scalalib.{Block, Context, Type, Value}

import java.lang.foreign.Arena

trait Bundle extends Data with DynamicSubfield:
  private[zaozi] var instantiating = true
  // valName -> BundleField
  private[zaozi] val _elements: collection.mutable.Map[String, BundleField[?]] =
    collection.mutable.Map[String, BundleField[?]]()
  def Flipped[T <: Data](
    tpe: T
  )(
    using TypeImpl,
    sourcecode.Name
  ): BundleField[T] = this.FlippedImpl(None, tpe)

  def Aligned[T <: Data](
    tpe: T
  )(
    using TypeImpl,
    sourcecode.Name
  ): BundleField[T] = this.AlignedImpl(None, tpe)

  def Flipped[T <: Data](
    name: String,
    tpe:  T
  )(
    using TypeImpl,
    sourcecode.Name
  ): BundleField[T] = this.FlippedImpl(Some(name), tpe)

  def Aligned[T <: Data](
    name: String,
    tpe:  T
  )(
    using TypeImpl,
    sourcecode.Name
  ): BundleField[T] = this.AlignedImpl(Some(name), tpe)

  def getRefViaFieldValName[E <: Data](
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
  ): Ref[E] = this.getRefViaFieldValNameImpl(
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
