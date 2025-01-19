// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.circt.scalalib.firrtl.capi.{
  given_DialectHandleApi,
  given_FirtoolOptionsApi,
  given_PassManagerApi,
  FirtoolOptions,
  FirtoolOptionsApi
}
import org.llvm.mlir.scalalib.{given_ContextApi, given_PassManagerApi, Context, ContextApi, PassManager, PassManagerApi}
import utest.*

import java.lang.foreign.Arena

class SIntSpecIO(
  using SimpleParameter)
    extends HWInterface[SimpleParameter]:
  val parameter  = summon[SimpleParameter]
  val a          = Flipped(SInt(parameter.width.W))
  val b          = Flipped(SInt(parameter.width.W))
  val c          = Flipped(UInt(parameter.width.W))
  val d          = Flipped(Bool())
  val sint       = Aligned(SInt((parameter.width + 1).W))
  val bits       = Aligned(Bits(parameter.width.W))
  val bool       = Aligned(Bool())
  val clock      = Flipped(Clock())
  val asyncReset = Flipped(AsyncReset())

class SIntSpecProbe(
  using SimpleParameter)
    extends DVInterface[SimpleParameter]

object SIntSpec extends TestSuite:
  val tests = Tests:
    given SimpleParameter(8, "SIntSpecModule")
    val out = new StringBuilder
    test("asBits"):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "assign bits = a;"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint.dontCare()
        io.bool.dontCare()
        io.bits := io.a.asBits
    test("+"):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "assign sint = {a[7], a} + {b[7], b};"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint := io.a + io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("-"):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "assign sint = {a[7], a} - {b[7], b};"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint := io.a - io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("*"):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "wire [15:0] tests = {{8{a[7]}}, a} * {{8{b[7]}}, b};"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint := ((io.a * io.b).asBits >> p.width).asSInt
        io.bool.dontCare()
        io.bits.dontCare()
    test("/"):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "assign sint = $signed($signed({a[7], a}) / $signed({b[7], b}));"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint := io.a / io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("%"):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "wire [7:0] tests = $signed($signed(a) % $signed(b));"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint := io.a % io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("<"):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "assign bool = $signed(a) < $signed(b);"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint.dontCare()
        io.bool := io.a < io.b
        io.bits.dontCare()
    test("<="):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "assign bool = $signed(a) <= $signed(b);"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint.dontCare()
        io.bool := io.a <= io.b
        io.bits.dontCare()
    test(">"):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "assign bool = $signed(a) > $signed(b);"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint.dontCare()
        io.bool := io.a > io.b
        io.bits.dontCare()
    test(">="):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "assign bool = $signed(a) >= $signed(b);"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint.dontCare()
        io.bool := io.a >= io.b
        io.bits.dontCare()
    test("==="):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "assign bool = a == b;"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint.dontCare()
        io.bool := io.a === io.b
        io.bits.dontCare()
    test("=/="):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "assign bool = a != b;"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint.dontCare()
        io.bool := io.a =/= io.b
        io.bits.dontCare()
    test("<< int"):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "assign sint = {a[6:0], 2'h0};"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint := (io.a << 2).asBits.bits(p.width, 0).asSInt
        io.bool.dontCare()
        io.bits.dontCare()
    test("<< uint"):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "wire [262:0] tests = {{255{a[7]}}, a} << c;",
        "assign sint = tests[8:0];"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint := (io.a << io.c).asBits.bits(p.width, 0).asSInt
        io.bool.dontCare()
        io.bits.dontCare()
    test(">> int"):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "assign sint = {{5{a[7]}}, a[7:4]};"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint := io.a >> 4
        io.bool.dontCare()
        io.bits.dontCare()
    test(">> uint"):
      verilogTest(new SIntSpecIO, new SIntSpecProbe)(
        "wire [7:0] tests = $signed($signed(a) >>> c);",
        "assign sint = {tests[7], tests};"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[SIntSpecIO]]
        io.sint := io.a >> io.c
        io.bool.dontCare()
        io.bits.dontCare()
