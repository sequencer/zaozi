// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import utest.*

class BitsSpecIO(
  using SimpleParameter)
    extends HWInterface[SimpleParameter]:
  val parameter  = summon[SimpleParameter]
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
  using SimpleParameter)
    extends DVInterface[SimpleParameter]

object BitsSpec extends TestSuite:
  val tests = Tests:
    given SimpleParameter(8, "BitsSpecModule")
    val out = new StringBuilder
    test("AsSInt"):
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
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
      verilogTest(new BitsSpecIO, new BitsSpecProbe)(
        "assign bits = {6'h0, a[4:3]};"
      ):
        val io = summon[Interface[BitsSpecIO]]
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a.bits(4, 3)
