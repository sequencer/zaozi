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

class UIntSpecIO(parameter: SimpleParameter) extends HWInterface[SimpleParameter](parameter):
  val a          = Flipped(UInt(parameter.width.W))
  val b          = Flipped(UInt(parameter.width.W))
  val c          = Flipped(UInt(parameter.width.W))
  val d          = Flipped(Bool())
  val uint       = Aligned(UInt((parameter.width + 1).W))
  val bits       = Aligned(Bits(parameter.width.W))
  val bool       = Aligned(Bool())
  val clock      = Flipped(Clock())
  val asyncReset = Flipped(AsyncReset())

class UIntSpecProbe(parameter: SimpleParameter) extends DVInterface[SimpleParameter](parameter)

object UIntSpec extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(8, "UIntSpecModule")
    val out       = new StringBuilder
    test("asBits"):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "assign bits = a;"
      ):
        val io = summon[Interface[UIntSpecIO]]
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits := io.a.asBits
    test("+"):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "assign uint = {1'h0, a} + {1'h0, b};"
      ):
        val io = summon[Interface[UIntSpecIO]]
        io.uint := io.a + io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("-"):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "assign uint = {1'h0, a} - {1'h0, b};"
      ):
        val io = summon[Interface[UIntSpecIO]]
        io.uint := io.a - io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("*"):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "assign uint = {1'h0, a} * {1'h0, b};"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[UIntSpecIO]]
        io.uint := (io.a * io.b).asBits.bits(p.width, 0).asUInt
        io.bool.dontCare()
        io.bits.dontCare()
    test("/"):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "assign uint = {1'h0, a / b};"
      ):
        val io = summon[Interface[UIntSpecIO]]
        io.uint := io.a / io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("%"):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "assign uint = {1'h0, a % b};"
      ):
        val io = summon[Interface[UIntSpecIO]]
        io.uint := io.a % io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("<"):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "assign bool = a < b;"
      ):
        val io = summon[Interface[UIntSpecIO]]
        io.uint.dontCare()
        io.bool := io.a < io.b
        io.bits.dontCare()
    test("<="):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "assign bool = a <= b;"
      ):
        val io = summon[Interface[UIntSpecIO]]
        io.uint.dontCare()
        io.bool := io.a <= io.b
        io.bits.dontCare()
    test(">"):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "assign bool = a > b;"
      ):
        val io = summon[Interface[UIntSpecIO]]
        io.uint.dontCare()
        io.bool := io.a > io.b
        io.bits.dontCare()
    test(">="):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "assign bool = a >= b;"
      ):
        val io = summon[Interface[UIntSpecIO]]
        io.uint.dontCare()
        io.bool := io.a >= io.b
        io.bits.dontCare()
    test("==="):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "assign bool = a == b;"
      ):
        val io = summon[Interface[UIntSpecIO]]
        io.uint.dontCare()
        io.bool := io.a === io.b
        io.bits.dontCare()
    test("=/="):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "assign bool = a != b;"
      ):
        val io = summon[Interface[UIntSpecIO]]
        io.uint.dontCare()
        io.bool := io.a =/= io.b
        io.bits.dontCare()
    test("<< int"):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "assign uint = {a[6:0], 2'h0};"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[UIntSpecIO]]
        io.uint := (io.a << 2).asBits.bits(p.width, 0).asUInt
        io.bool.dontCare()
        io.bits.dontCare()
    test("<< uint"):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "wire [262:0] tests = {255'h0, a} << b;",
        "assign uint = tests[8:0];"
      ):
        val p  = summon[SimpleParameter]
        val io = summon[Interface[UIntSpecIO]]
        io.uint := (io.a << io.b).asBits.bits(p.width, 0).asUInt
        io.bool.dontCare()
        io.bits.dontCare()
    test(">> int"):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "assign uint = {5'h0, a[7:4]};"
      ):
        val io = summon[Interface[UIntSpecIO]]
        io.uint := io.a >> 4
        io.bool.dontCare()
        io.bits.dontCare()
    test(">> uint"):
      verilogTest(parameter, UIntSpecIO(parameter), UIntSpecProbe(parameter))(
        "assign uint = {1'h0, a >> b};"
      ):
        val io = summon[Interface[UIntSpecIO]]
        io.uint := io.a >> io.b
        io.bool.dontCare()
        io.bits.dontCare()
