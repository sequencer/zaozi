// SPDX-License-Identifier: Apache-2.0
package me.jiuyang.zaozi.circt.firrtl

import org.llvm.circt.scalalib.{FirrtlBundleField as CirctFirrtlBundleField, given}
import org.llvm.mlir.scalalib.{Context as MlirContext, Type as MlirType}

import java.lang.foreign.Arena

given BundleFieldApi with
  extension (bundleField: CirctFirrtlBundleField) inline def asBundleField: BundleField = ???
end given

given FirrtlTypeApi with
  extension (tpe: MlirType)
    inline def toFirrtlType(
      using Arena
    ): FirrtlType =
      if (tpe.isClock) tpe.asClock
      else if (tpe.isReset) tpe.asReset
      else if (tpe.isAsyncReset) tpe.asAsyncReset
      else if (tpe.isUInt) tpe.asUInt
      else if (tpe.isSInt) tpe.asSInt
      else if (tpe.isAnalog) tpe.asAnalog
      else if (tpe.isBundle) tpe.asBundle
      else if (tpe.isVector) tpe.asVector
      else throw new Exception("Unmatched FirrtlType")
    inline def asClock:      Clock      =
      require(tpe.isClock)
      // TODO: tpe.isForceable
      Clock(tpe.isConst, tpe.isRef, false)
    inline def asReset:      Reset      =
      require(tpe.isReset)
      Reset(tpe.isConst, tpe.isRef, false)
    inline def asAsyncReset: AsyncReset =
      require(tpe.isAsyncReset)
      AsyncReset(tpe.isConst, tpe.isRef, false)
    inline def asUInt:       UInt       =
      require(tpe.isUInt)
      UInt(tpe.width(true).toInt, tpe.isConst, tpe.isRef, false)
    inline def asSInt:       SInt       =
      require(tpe.isSInt)
      SInt(tpe.width(true).toInt, tpe.isConst, tpe.isRef, false)
    inline def asAnalog:     Analog     =
      require(tpe.isAnalog)
      Analog(tpe.width(true).toInt, tpe.isConst, tpe.isRef, false)
    inline def asBundle(
      using Arena
    ): Bundle =
      require(tpe.isBundle)
      Bundle(Seq.tabulate(tpe.getBundleNumFields.toInt)(i => tpe.getBundleFieldByIndex(i).asBundleField), tpe.isConst)
    inline def asVector(
      using Arena
    ): Vector =
      require(tpe.isVector)
      Vector(tpe.getElementType.toFirrtlType, tpe.getBundleNumFields.toInt, tpe.isConst)
end given

inline def toMlir(
  bundleField: BundleField
)(
  using Arena,
  MlirContext
): CirctFirrtlBundleField =
  val bundleFieldApi = summon[org.llvm.circt.scalalib.FirrtlBundleFieldApi]
  bundleFieldApi.createFirrtlBundleField(bundleField.name, bundleField.isFlip, toMlir(bundleField.tpe))

inline def toMlir[T <: FirrtlType](
  tpe: T
)(
  using Arena,
  MlirContext
): MlirType =
  val typeApi = summon[org.llvm.circt.scalalib.TypeApi]
  tpe match
    case tpe: Clock      => 
      val tpe = typeApi.getClock
      tpe
    case tpe: Reset      => 
      typeApi.getReset
    case tpe: AsyncReset => 
      typeApi.getAsyncReset
    case tpe: UInt       => 
      tpe.width.getUInt
    case tpe: SInt       => 
      tpe.width.getSInt
    case tpe: Analog     => 
      tpe.width.getAnolog
    case tpe: Bundle     => 
      tpe.fields.map(toMlir).getBundle
    case tpe: Vector     => 
      toMlir(tpe.element).getVector(tpe.count)
