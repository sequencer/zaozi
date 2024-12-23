// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.circtlib.MlirValue
import me.jiuyang.zaozi.internal.{Context, firrtl}
import sourcecode.{File, Line, Name}

case class BundleField[T <: Data](name: String, isFlip: Boolean, tpe: T)

trait BundleLike:
  def elements:   Seq[BundleField[?]]
  def firrtlType: firrtl.Bundle =
    new firrtl.Bundle(elements.map(bf => firrtl.BundleField(bf.name, bf.isFlip, bf.tpe.firrtlType)), false)

class Record(override val elements: Seq[BundleField[?]]) extends Data with BundleLike

trait Bundle extends Data with BundleLike with DynamicSubfield:
  /** The Bundle is still instantiating at user code. */
  private var instantiating = true

  private[zaozi] val _elements: collection.mutable.Map[String, BundleField[?]] =
    collection.mutable.Map[String, BundleField[?]]()
  protected def Aligned[T <: Data](
    data:          T
  )(
    using valName: sourcecode.Name
  ): BundleField[T] = createBundleField(
    name = None,
    valName = valName.value,
    isFlip = false,
    data = data
  )

  protected def Flipped[T <: Data](
    data:          T
  )(
    using valName: sourcecode.Name
  ): BundleField[T] = createBundleField(
    name = None,
    valName = valName.value,
    isFlip = true,
    data = data
  )

  protected def Aligned[T <: Data](
    name:          String,
    data:          T
  )(
    using valName: sourcecode.Name
  ): BundleField[T] =
    createBundleField(
      name = Some(name),
      valName = valName.value,
      isFlip = false,
      data = data
    )

  protected def Flipped[T <: Data](
    name:          String,
    data:          T
  )(
    using valName: sourcecode.Name
  ): BundleField[T] =
    createBundleField(
      name = Some(name),
      valName = valName.value,
      isFlip = true,
      data = data
    )

  private def createBundleField[T <: Data](
    name:    Option[String],
    valName: String,
    isFlip:  Boolean,
    data:    T
  ): BundleField[T] =
    require(instantiating, s"$toString is closed")
    val bf = BundleField(name.getOrElse(valName), isFlip, data)
    _elements += (valName -> bf)
    bf

  final lazy val elements: Seq[BundleField[?]] =
    val ele = _elements.values.toSeq
    instantiating = false
    ele

  def getRefViaFieldValName[E <: Data](
    refer:        MlirValue,
    fieldValName: String,
    ctx:          Context,
    file:         File,
    line:         Line,
    valName:      Name
  ): Ref[E] =
    def valNameToRefName(valName: String): String =
      _elements
        .getOrElse(valName, throw new Exception(s"$valName not found in ${_elements.keys}"))
        .name

    def valNameToTpe[T <: Data](valName: String): T =
      _elements(valName).tpe.asInstanceOf[T]

    val idx       = ctx.handler.firrtlTypeGetBundleFieldIndex(
      firrtlType.toMLIR(ctx.handler),
      valNameToRefName(fieldValName)
    )
    val subaccess = ctx.handler
      .OpBuilder("firrtl.subfield", ctx.currentBlock, ctx.handler.unkLoc)
      .withNamedAttr("fieldIndex", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), idx))
      .withOperand(refer)
      .withResultInference(1)
      .build()
      .results
      .head
    new Ref[E](subaccess, valNameToTpe(fieldValName))
