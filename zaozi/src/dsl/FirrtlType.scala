// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.internal.firrtl

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.circtlib.{CirctHandler, FIRRTLBundleField, MlirType}

case class BundleField(name: String, isFlip: Boolean, tpe: FirrtlType)

/** It maintains the data structure match to firrtl dialect.  */
sealed case class FirrtlType(
  tpeName: String,
  const:   Boolean,
  width:   Option[Width],
  fields:  Option[Seq[BundleField]],
  element: Option[FirrtlType],
  count: Option[Int]) {
  def toMLIR(
    handler: CirctHandler
  ): MlirType = tpeName match
    case s if s == "clock"      => handler.firrtlTypeGetClock()
    case s if s == "reset"      => handler.firrtlTypeGetReset()
    case s if s == "asyncreset" => handler.firrtlTypeGetAsyncReset()
    case s if s == "uint"       => handler.firrtlTypeGetUInt(width.get.get)
    case s if s == "sint"       => handler.firrtlTypeGetSInt(width.get.get)
    case s if s == "analog"     => handler.firrtlTypeGetAnalog(width.get.get)
    case s if s == "bundle"     =>
      handler.firrtlTypeGetBundle(fields.get.map(f => FIRRTLBundleField(f.name, f.isFlip, f.tpe.toMLIR(handler))))
    case s if s == "vector"     => handler.firrtlTypeGetVector(element.get.toMLIR(handler), count.get)
}

class Clock(const: Boolean)                extends FirrtlType("clock", const, None, None, None, None)
class Reset(const: Boolean)                extends FirrtlType("reset", const, None, None, None, None)
class AsyncReset(const: Boolean)           extends FirrtlType("asyncreset", const, None, None, None, None)
class UInt(width: Width, const: Boolean)   extends FirrtlType("uint", const, Some(width), None, None, None)
class SInt(width: Width, const: Boolean)   extends FirrtlType("sint", const, Some(width), None, None, None)
class Analog(width: Width, const: Boolean) extends FirrtlType("analog", const, Some(width), None, None, None)
class Bundle(fields: Seq[BundleField], const: Boolean)
    extends FirrtlType("bundle", const, None, Some(fields), None, None)
class Vector(element: FirrtlType, count: Int, const: Boolean)
    extends FirrtlType("vector", const, None, None, Some(element), Some(count))
