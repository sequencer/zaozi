// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import utest.*

class BitsSpecInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter):
  def moduleName: String = parameter.moduleName
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

object BitsSpec extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(8, "BitsSpecModule")
    val out       = new StringBuilder
    test("AsSInt"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign sint = a;"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.sint := io.a.asSInt
    test("AsUInt"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign uint = a;"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.uint := io.a.asUInt
    test("~"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bits = ~a;"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := ~io.a
    test("&"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bool = &a;"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bool := io.a.andR
    test("OrR"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bool = |a;"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bool := io.a.orR
    test("XorR"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bool = ^a;"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bool := io.a.xorR
    test("==="):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bool = a == b;"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bool := io.a === io.b
    test("=/="):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bool = a != b;"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bool := io.a =/= io.b
    test("&"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bits = a & b;"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a & io.b
    test("|"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bits = a | b;"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a | io.b
    test("^"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bits = a ^ b;"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a ^ io.b
    test("Cat"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign widenBits = {a, b};"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.widenBits := io.a ## io.b
    test("<< int"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bits = {a[5:0], 2'h0};"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := (io.a << 2).bits(p.width - 1, 0)
    test("<< uint"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "wire [262:0] tests = {255'h0, a} << c;",
        "assign bits = tests[7:0];"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := (io.a << io.c).bits(p.width - 1, 0)
    test(">> int"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bits = {4'h0, a[7:4]};"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a >> 4
    test(">> uint"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bits = a >> c;"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a >> io.c
    test("Head"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bits = {a[7:4], 4'h0};"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a.head(4) ## 0.B(4.W)
    test("Tail"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bits = {a[3:0], 4'h0};"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a.tail(4) ## 0.B(4.W)
    test("Pad"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bits = {4'h0, a[3:0]};"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a.tail(4).pad(4)
    test("Pad"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bits = {4'h0, a[3:0]};"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a.tail(4).pad(4)
    test("ExtractRange"):
      verilogTest(parameter, BitsSpecInterface(parameter))(
        "assign bits = {6'h0, a[4:3]};"
      ): (p: SimpleParameter, io: Wire[BitsSpecInterface]) =>
        io.sint.dontCare()
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits.dontCare()
        io.widenBits.dontCare()
        io.bits := io.a.bits(4, 3)
