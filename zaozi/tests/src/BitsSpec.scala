// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import utest.*

class BitsSpecIO(parameter: SimpleParameter) extends HWInterface[SimpleParameter](parameter):
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

class BitsSpecProbe(parameter: SimpleParameter) extends DVInterface[SimpleParameter](parameter)

object BitsSpec extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(8, "BitsSpecModule")
    val out       = new StringBuilder
    test("AsSInt"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign sint = a;"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.sint := io.a.asSInt
    test("AsUInt"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign uint = a;"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.uint := io.a.asUInt
    test("~"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bits = ~a;"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := ~io.a
    test("&"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bool = &a;"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bool := io.a.andR
    test("OrR"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bool = |a;"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bool := io.a.orR
    test("XorR"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bool = ^a;"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bool := io.a.xorR
    test("==="):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bool = a == b;"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bool := io.a === io.b
    test("=/="):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bool = a != b;"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bool := io.a =/= io.b
    test("&"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bits = a & b;"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a & io.b
    test("|"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bits = a | b;"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a | io.b
    test("^"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bits = a ^ b;"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a ^ io.b
    test("Cat"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign widenBits = {a, b};"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.widenBits := io.a ## io.b
    test("<< int"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bits = {a[5:0], 2'h0};"
      ):
        val io = summon[Interface[BitsSpecIO]]
        val p  = summon[SimpleParameter]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := (io.a << 2).bits(p.width - 1, 0)
    test("<< uint"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "wire [262:0] tests = {255'h0, a} << c;",
        "assign bits = tests[7:0];"
      ):
        val io = summon[Interface[BitsSpecIO]]
        val p  = summon[SimpleParameter]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := (io.a << io.c).bits(p.width - 1, 0)
    test(">> int"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bits = {4'h0, a[7:4]};"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a >> 4
    test(">> uint"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bits = a >> c;"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a >> io.c
    test("Head"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bits = {a[7:4], 4'h0};"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a.head(4) ## 0.B(4.W)
    test("Tail"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bits = {a[3:0], 4'h0};"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a.tail(4) ## 0.B(4.W)
    test("Pad"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bits = {4'h0, a[3:0]};"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a.tail(4).pad(4)
    test("Pad"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bits = {4'h0, a[3:0]};"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a.tail(4).pad(4)
    test("ExtractRange"):
      verilogTest(parameter, BitsSpecIO(parameter), BitsSpecProbe(parameter))(
        "assign bits = {6'h0, a[4:3]};"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a.bits(4, 3)
