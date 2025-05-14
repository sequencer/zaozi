// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*

import org.llvm.circt.scalalib.firrtl.capi.given_DialectHandleApi
import org.llvm.mlir.scalalib.{given_ContextApi, Context, ContextApi}

import java.lang.foreign.Arena
import utest.*
import me.jiuyang.zaozi.magic.macros.generator

case class BitsSpecParameter(width: Int) extends Parameter
given upickle.default.ReadWriter[BitsSpecParameter] = upickle.default.macroRW

class BitsSpecIO(
  parameter: BitsSpecParameter)
    extends HWInterface[BitsSpecParameter](parameter):
  val a          = Flipped(Bits(parameter.width.W))
  val b          = Flipped(Bits(parameter.width.W))
  val c          = Flipped(UInt(parameter.width.W))
  val d          = Flipped(Bool())
  val sint       = Aligned(SInt((parameter.width).W))
  val uint       = Aligned(UInt((parameter.width).W))
  val bits       = Aligned(Bits(parameter.width.W))
  val widenBits  = Aligned(Bits((2 * parameter.width).W))
  val bool       = Aligned(Bool())
  val clock      = Flipped(Clock())
  val asyncReset = Flipped(AsyncReset())

class BitsSpecProbe(
  parameter: BitsSpecParameter)
    extends DVInterface[BitsSpecParameter](parameter)

object BitsSpec extends TestSuite:
  val tests = Tests:
    test("AsSInt"):
      @generator
      object AsSInt extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.sint := io.a.asSInt
      AsSInt.verilogTest(BitsSpecParameter(8))(
        "assign sint = a;"
      )

    test("AsUInt"):
      @generator
      object AsUInt extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.uint := io.a.asUInt
      AsUInt.verilogTest(BitsSpecParameter(8))(
        "assign uint = a;"
      )

    test("~"):
      @generator
      object Not extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := ~io.a
      Not.verilogTest(BitsSpecParameter(8))(
        "assign bits = ~a;"
      )

    test("& (reduce)"):
      @generator
      object AndR extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bool := io.a.andR
      AndR.verilogTest(BitsSpecParameter(8))(
        "assign bool = &a;"
      )

    test("OrR"):
      @generator
      object OrR extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bool := io.a.orR
      OrR.verilogTest(BitsSpecParameter(8))(
        "assign bool = |a;"
      )

    test("XorR"):
      @generator
      object XorR extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bool := io.a.xorR
      XorR.verilogTest(BitsSpecParameter(8))(
        "assign bool = ^a;"
      )

    test("==="):
      @generator
      object Eq extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bool := io.a === io.b
      Eq.verilogTest(BitsSpecParameter(8))(
        "assign bool = a == b;"
      )

    test("=/="):
      @generator
      object Neq extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bool := io.a =/= io.b
      Neq.verilogTest(BitsSpecParameter(8))(
        "assign bool = a != b;"
      )

    test("&"):
      @generator
      object And extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := io.a & io.b
      And.verilogTest(BitsSpecParameter(8))(
        "assign bits = a & b;"
      )

    test("|"):
      @generator
      object Or extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := io.a | io.b
      Or.verilogTest(BitsSpecParameter(8))(
        "assign bits = a | b;"
      )

    test("^"):
      @generator
      object Xor extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := io.a ^ io.b
      Xor.verilogTest(BitsSpecParameter(8))(
        "assign bits = a ^ b;"
      )

    test("Cat"):
      @generator
      object Cat extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.widenBits := io.a ## io.b
      Cat.verilogTest(BitsSpecParameter(8))(
        "assign widenBits = {a, b};"
      )

    test("<< int"):
      @generator
      object ShiftLeftInt extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          val p  = parameter
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := (io.a << 2).bits(p.width - 1, 0)
      ShiftLeftInt.verilogTest(BitsSpecParameter(8))(
        "assign bits = {a[5:0], 2'h0};"
      )

    test("<< uint"):
      @generator
      object ShiftLeftUInt extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          val p  = parameter
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := (io.a << io.c).bits(p.width - 1, 0)
      ShiftLeftUInt.verilogTest(BitsSpecParameter(8))(
        "wire [262:0] _GEN_0 = {255'h0, a} << c;",
        "assign bits = _GEN_0[7:0];"
      )

    test(">> int"):
      @generator
      object ShiftRightInt extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := io.a >> 4
      ShiftRightInt.verilogTest(BitsSpecParameter(8))(
        "assign bits = {4'h0, a[7:4]};"
      )

    test(">> uint"):
      @generator
      object ShiftRightUInt extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := io.a >> io.c
      ShiftRightUInt.verilogTest(BitsSpecParameter(8))(
        "assign bits = a >> c;"
      )

    test("Head"):
      @generator
      object Head extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := io.a.head(4) ## 0.B(4.W)
      Head.verilogTest(BitsSpecParameter(8))(
        "assign bits = {a[7:4], 4'h0};"
      )

    test("Tail"):
      @generator
      object Tail extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := io.a.tail(4) ## 0.B(4.W)
      Tail.verilogTest(BitsSpecParameter(8))(
        "assign bits = {a[3:0], 4'h0};"
      )

    test("Pad"):
      @generator
      object Pad1 extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := io.a.tail(4).pad(4)
      Pad1.verilogTest(BitsSpecParameter(8))(
        "assign bits = {4'h0, a[3:0]};"
      )

    test("Pad"):
      @generator
      object Pad2 extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := io.a.tail(4).pad(4)
      Pad2.verilogTest(BitsSpecParameter(8))(
        "assign bits = {4'h0, a[3:0]};"
      )

    test("ExtractRange"):
      @generator
      object ExtractRange extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := io.a.bits(4, 3)
      ExtractRange.verilogTest(BitsSpecParameter(8))(
        "assign bits = {6'h0, a[4:3]};"
      )

    test("ExtractRange apply"):
      @generator
      object ExtractRangeApply extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := io.a(4, 3)
      ExtractRangeApply.verilogTest(BitsSpecParameter(8))(
        "assign bits = {6'h0, a[4:3]};"
      )

    test("Named ExtractRange apply"):
      @generator
      object NamedExtractRangeApply extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := io.a(hi = 4, lo = 3)
      NamedExtractRangeApply.verilogTest(BitsSpecParameter(8))(
        "assign bits = {6'h0, a[4:3]};"
      )

    test("ExtractElement"):
      @generator
      object ExtractElement extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := io.a.bit(4)
      ExtractElement.verilogTest(BitsSpecParameter(8))(
        "assign bits = {7'h0, a[4]};"
      )

    test("ExtractElement apply"):
      @generator
      object ExtractElementApply extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := io.a(4)
      ExtractElementApply.verilogTest(BitsSpecParameter(8))(
        "assign bits = {7'h0, a[4]};"
      )

    test("Named ExtractElement apply"):
      @generator
      object NamedExtractElementApply
          extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe]
          with HasVerilogTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          io.sint.dontCare()
          io.uint.dontCare()
          io.bool.dontCare()
          io.bits.dontCare()
          io.widenBits.dontCare()
          io.bits := io.a(idx = 4)
      NamedExtractElementApply.verilogTest(BitsSpecParameter(8))(
        "assign bits = {7'h0, a[4]};"
      )

    test("Apply with wrong data type"):
      @generator
      object ApplyWithWrongDataType
          extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe]
          with HasCompileErrorTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          compileError("""io.bits := io.c(1)""").check(
            "",
            "Element type must be Bits, but got me.jiuyang.zaozi.valuetpe.UInt."
          )
      ApplyWithWrongDataType.compileErrorTest(BitsSpecParameter(8))

    test("Apply with incorrect named argument"):
      @generator
      object ApplyWithIncorrectNamedArgument
          extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe]
          with HasCompileErrorTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          compileError("""io.bits := io.a(invalid_arg = 4)""").check(
            "",
            "Unexpected named arguments invalid_arg."
          )
          compileError("""io.bits := io.a(idx = 1, invalid_arg = 4)""").check(
            "",
            "Unexpected named arguments (idx, invalid_arg)."
          )
      ApplyWithIncorrectNamedArgument.compileErrorTest(BitsSpecParameter(8))

    test("Apply with incorrect number of arguments"):
      @generator
      object ApplyWithIncorrectNumberOfArguments
          extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe]
          with HasCompileErrorTest:
        def architecture(parameter: BitsSpecParameter) =
          val io = summon[Interface[BitsSpecIO]]
          compileError("""io.bits := io.b(1, 2, 3)""").check(
            "",
            "Expected 1 or 2 args, but got 3"
          )
      ApplyWithIncorrectNumberOfArguments.compileErrorTest(BitsSpecParameter(8))
