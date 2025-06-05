// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.Interface
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.mlir.scalalib.capi.ir.{given_ContextApi, Context, ContextApi}
import utest.*

import java.lang.foreign.Arena

class TypeParamIO[A <: Bundle, B <: Bundle](_a: A, _b: B) extends Bundle:
  val a = Flipped(_a)
  val b = Flipped(_b)

class SimpleBundle extends Bundle:
  val g = Aligned(UInt(32.W))

class SimpleBundleA extends Bundle:
  val a = Aligned(UInt(32.W))

class SimpleBundleB extends Bundle:
  val b = Aligned(UInt(32.W))

case class BundleSpecParameter(width: Int) extends Parameter
given upickle.default.ReadWriter[BundleSpecParameter] = upickle.default.macroRW

class BundleSpecLayers(parameter: BundleSpecParameter) extends LayerInterface(parameter)

class BundleSpecIO(parameter: BundleSpecParameter) extends HWInterface(parameter):
  val a = Aligned(UInt(parameter.width.W))
  val b = Flipped(UInt(parameter.width.W))
  val c = Aligned(new Bundle {
    val d = Aligned(UInt(parameter.width.W))
  })
  val f = Flipped(new SimpleBundle)
  val e = UInt(parameter.width.W)
  val i = parameter.width
  val j = Aligned(new TypeParamIO(new SimpleBundleA, new SimpleBundleB))
  val k = Option.when(parameter.width >= 16)(Aligned(UInt(parameter.width.W)))

class BundleSpecProbe(parameter: BundleSpecParameter)
    extends DVInterface[BundleSpecParameter, BundleSpecLayers](parameter)

object BundleSpec extends TestSuite:
  val tests = Tests:
    test("Bundle in Bundle should work"):
      @generator
      object BundleInBundleShouldWork
          extends Generator[BundleSpecParameter, BundleSpecLayers, BundleSpecIO, BundleSpecProbe]
          with HasFirrtlTest:
        def architecture(parameter: BundleSpecParameter) =
          val io = summon[Interface[BundleSpecIO]]
          io.a := io.f.g
      BundleInBundleShouldWork.firrtlTest(BundleSpecParameter(32))(
        "connect io.a, io.f.g"
      )

    test("Bundle with type parameter should work"):
      @generator
      object BundleWithTypeParameterShouldWork
          extends Generator[BundleSpecParameter, BundleSpecLayers, BundleSpecIO, BundleSpecProbe]
          with HasFirrtlTest:
        def architecture(parameter: BundleSpecParameter) =
          val io = summon[Interface[BundleSpecIO]]
          io.a := io.j.a.a
      BundleWithTypeParameterShouldWork.firrtlTest(BundleSpecParameter(32))(
        "connect io.a, io.j.a.a"
      )

    test("Symbol found"):
      @generator
      object SymbolFound
          extends Generator[BundleSpecParameter, BundleSpecLayers, BundleSpecIO, BundleSpecProbe]
          with HasFirrtlTest:
        def architecture(parameter: BundleSpecParameter) =
          val io = summon[Interface[BundleSpecIO]]
          io.a := io.b
      SymbolFound.firrtlTest(BundleSpecParameter(32))(
        "connect io.a, io.b"
      )

    test("Optional field"):
      @generator
      object OptionalField
          extends Generator[BundleSpecParameter, BundleSpecLayers, BundleSpecIO, BundleSpecProbe]
          with HasFirrtlTest:
        def architecture(parameter: BundleSpecParameter) =
          val io = summon[Interface[BundleSpecIO]]
          io.k.foreach(_ := io.b)
      OptionalField.firrtlTest(BundleSpecParameter(32))(
        "connect io.k, io.b"
      )
      OptionalField.firrtlTest(BundleSpecParameter(8))(out => !out.contains("connect io.k, io.b"))

    test("Subaccess on non-Bundle type"):
      @generator
      object SubaccessOnNonBundleType
          extends Generator[BundleSpecParameter, BundleSpecLayers, BundleSpecIO, BundleSpecProbe]
          with HasCompileErrorTest:
        def architecture(parameter: BundleSpecParameter) =
          val io = summon[Interface[BundleSpecIO]]
          compileError("""io.a.a""").check(
            "",
            "Type parameter T must be a subtype of DynamicSubfield, but got me.jiuyang.zaozi.valuetpe.UInt."
          )
      SubaccessOnNonBundleType.compileErrorTest(BundleSpecParameter(32))

    test("Symbol not found"):
      @generator
      object SymbolNotFound
          extends Generator[BundleSpecParameter, BundleSpecLayers, BundleSpecIO, BundleSpecProbe]
          with HasCompileErrorTest:
        def architecture(parameter: BundleSpecParameter) =
          val io = summon[Interface[BundleSpecIO]]
          compileError("""io.fourzerofour""").check(
            "",
            "Field 'fourzerofour' does not exist in type me.jiuyang.zaozi.tests.BundleSpecIO."
          )
      SymbolNotFound.compileErrorTest(BundleSpecParameter(32))

    test("Access non Data type - Int"):
      @generator
      object AccessNonDataTypeInt
          extends Generator[BundleSpecParameter, BundleSpecLayers, BundleSpecIO, BundleSpecProbe]
          with HasCompileErrorTest:
        def architecture(parameter: BundleSpecParameter) =
          val io = summon[Interface[BundleSpecIO]]
          compileError("""io.i""").check(
            "",
            "Field type 'scala.Int' does not conform to the upper bound BundleField."
          )
      AccessNonDataTypeInt.compileErrorTest(BundleSpecParameter(32))

    test("Access non Data type - UInt"):
      @generator
      object AccessNonDataTypeUInt
          extends Generator[BundleSpecParameter, BundleSpecLayers, BundleSpecIO, BundleSpecProbe]
          with HasCompileErrorTest:
        def architecture(parameter: BundleSpecParameter) =
          val io = summon[Interface[BundleSpecIO]]
          compileError("""io.e""").check(
            "",
            "Field type 'me.jiuyang.zaozi.valuetpe.UInt' does not conform to the upper bound BundleField."
          )
      AccessNonDataTypeUInt.compileErrorTest(BundleSpecParameter(32))

    test("Structural Type doesn't work"):
      @generator
      object StructuralTypeDoesntWork
          extends Generator[BundleSpecParameter, BundleSpecLayers, BundleSpecIO, BundleSpecProbe]
          with HasCompileErrorTest:
        def architecture(parameter: BundleSpecParameter) =
          val io = summon[Interface[BundleSpecIO]]
          compileError("""io.c.d""").check(
            "",
            "Field 'd' does not exist in type me.jiuyang.zaozi.valuetpe.Bundle."
          )
      StructuralTypeDoesntWork.compileErrorTest(BundleSpecParameter(32))
