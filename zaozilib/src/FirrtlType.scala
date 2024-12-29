// SPDX-License-Identifier: Apache-2.0
package me.jiuyang.zaozi.circt.firrtl

import org.llvm.circt.scalalib.FirrtlBundleField as CirctFirrtlBundleField
import org.llvm.mlir.scalalib.Type as MlirType

import java.lang.foreign.Arena

trait FirrtlType
case class Clock(const: Boolean, ref: Boolean, refRw: Boolean)                                   extends FirrtlType
case class Reset(const: Boolean, ref: Boolean, refRw: Boolean)                                   extends FirrtlType
case class AsyncReset(const: Boolean, ref: Boolean, refRw: Boolean)                              extends FirrtlType
case class UInt(width: Int, const: Boolean, ref: Boolean, refRw: Boolean)                        extends FirrtlType
case class SInt(width: Int, const: Boolean, ref: Boolean, refRw: Boolean)                        extends FirrtlType
case class Analog(width: Int, const: Boolean, ref: Boolean, refRw: Boolean)                      extends FirrtlType
case class BundleField(name: String, isFlip: Boolean, tpe: FirrtlType)
case class Bundle(fields: Seq[BundleField], const: Boolean)        extends FirrtlType
case class Vector(element: FirrtlType, count: Int, const: Boolean) extends FirrtlType

trait BundleFieldApi:
  extension (bundleField: CirctFirrtlBundleField) inline def asBundleField: BundleField

trait FirrtlTypeApi:
  extension (tpe: MlirType)
    inline def toFirrtlType(
      using Arena
    ):                       FirrtlType
    inline def asClock:      Clock
    inline def asReset:      Reset
    inline def asAsyncReset: AsyncReset
    inline def asUInt:       UInt
    inline def asSInt:       SInt
    inline def asAnalog:     Analog
    inline def asBundle(
      using Arena
    ):                       Bundle
    inline def asVector(
      using Arena
    ):                       Vector
