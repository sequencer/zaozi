// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.internal.{firrtl, Context}

trait Data:
  // only accessed by Builder.
  def firrtlType: firrtl.FirrtlType

object Clock:
  def apply(): Clock = new Clock
class Clock extends Data:
  def firrtlType = new firrtl.Clock(false)
// Don't support abstract Reset type, that's cancer
object Reset:
  def apply(): Reset = new Reset
type Reset = Bool
object AsyncReset:
  def apply(): AsyncReset = new AsyncReset
class AsyncReset extends Data:
  def firrtlType = new firrtl.AsyncReset(false)

object Bool:
  def apply(): Bool = new Bool
class Bool extends Data:
  def firrtlType = new firrtl.UInt(1.W, false)
object UInt:
  def apply(width: Width): UInt = new UInt(width)
class UInt(width: Width) extends Data:
  def firrtlType = new firrtl.UInt(width, false)
object SInt:
  def apply(width: Width): SInt = new SInt(width)
class SInt(width: Width) extends Data:
  def firrtlType = new firrtl.SInt(width, false)
object Analog:
  def apply(width: Width): Analog = new Analog(width)
class Analog(width: Width) extends Data:
  def firrtlType = new firrtl.Analog(width, false)
case class BundleField(name: String, isFlip: Boolean, tpe: Data)
abstract class Bundle extends Data:
  def Aligned(name: String, data: Data): Unit                                        =
    elements += BundleField(name, false, data)
  def Flipped(name: String, data: Data): Unit                                        =
    elements += BundleField(name, true, data)
  val elements:                          collection.mutable.ArrayBuffer[BundleField] = collection.mutable.ArrayBuffer[BundleField]()
  def firrtlType:                        firrtl.Bundle                               =
    new firrtl.Bundle(elements.toSeq.map(bf => firrtl.BundleField(bf.name, bf.isFlip, bf.tpe.firrtlType)), false)
object Vec:
  def fill[E <: Data](n: Int)(element: E): Vec[E] = new Vec(element, n)
class Vec[E <: Data](element: E, count: Int) extends Data:
  def firrtlType = new firrtl.Vector(element.firrtlType, count, false)

trait SourceInfo

given [D <: Data, SRC <: Referable[D], SINK <: Referable[D]]: MonoConnect[D, SRC, SINK] with
  extension (ref: SINK)
    def :=(
      that:      SRC
    )(
      using ctx: Context
    ): Unit =
      ctx.handler
        .OpBuilder("firrtl.connect", ctx.currentBlock, ctx.handler.unkLoc)
        .withOperand( /* dest */ ref.refer)
        .withOperand( /* src */ that.refer)
        .build()

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

given ToConstUInt[BigInt] with
  extension (ref: BigInt)
    def U(
      width:     Width
    )(
      using ctx: Context
    ): Const[UInt] =
      val tpe     = UInt(width)
      val mlirTpe = tpe.firrtlType.toMLIR(ctx.handler)
      val const   = ctx.handler
        .OpBuilder("firrtl.constant", ctx.currentBlock, ctx.handler.unkLoc)
        .withNamedAttr(
          "value",
          ctx.handler.firrtlAttrGetIntegerFromString(
            mlirTpe,
            if (width.unknown) math.max(ref.bitLength, 1) else width.get,
            ref.toString,
            10
          )
        )
        // TODO: circt should support type infer for firrtl.constant
        .withResult(mlirTpe)
        .build()
        .results
        .head
      new Const(const, UInt(width))

given ToConstUInt[Int] with
  extension (ref: Int)
    def U(
      width:     Width
    )(
      using ctx: Context
    ): Const[UInt] = BigInt(ref).U(width)
