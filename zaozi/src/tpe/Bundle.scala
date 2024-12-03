// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.internal.{firrtl, Context}

case class BundleField(name: String, isFlip: Boolean, tpe: Data)
abstract class Bundle extends Data:
  def Aligned[T <: Data](name: String, data: T): T =
    elements += BundleField(name, false, data)
    data
  def Flipped[T <: Data](name: String, data: T): T =
    elements += BundleField(name, true, data)
    data

  val elements:   collection.mutable.ArrayBuffer[BundleField] = collection.mutable.ArrayBuffer[BundleField]()
  def firrtlType: firrtl.Bundle                               =
    new firrtl.Bundle(elements.toSeq.map(bf => firrtl.BundleField(bf.name, bf.isFlip, bf.tpe.firrtlType)), false)

given [T <: Bundle, R <: Referable[T]]: Subaccess[T, R] with
  extension (ref: R)
    def field(
      that:      String
    )(
      using ctx: Context
    ): Ref[Data] =
      val idx       = ctx.handler.firrtlTypeGetBundleFieldIndex(ref.tpe.firrtlType.toMLIR(ctx.handler), that)
      val tpe       = ref.tpe.elements(idx).tpe
      val subaccess = ctx.handler
        .OpBuilder("firrtl.subfield", ctx.currentBlock, ctx.handler.unkLoc)
        .withNamedAttr("fieldIndex", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), idx))
        .withOperand(ref.refer)
        .withResultInference(1)
        .build()
        .results
        .head
      new Ref[Data](subaccess, tpe)
