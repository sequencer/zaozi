// SPDX-License-Identifier: Apache-2.0

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

class UIntSpecInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter):
  def moduleName: String = parameter.moduleName
  val a          = Flipped(UInt(parameter.width.W))
  val b          = Flipped(UInt(parameter.width.W))
  val c          = Flipped(UInt(parameter.width.W))
  val d          = Flipped(Bool())
  val uint       = Aligned(UInt((parameter.width + 1).W))
  val bits       = Aligned(Bits(parameter.width.W))
  val bool       = Aligned(Bool())
  val clock      = Flipped(Clock())
  val asyncReset = Flipped(AsyncReset())

object UIntSpec extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(8, "UIntSpecModule")
    val out       = new StringBuilder
    test("asBits"):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "assign bits = a;"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits := io.a.asBits
    test("+"):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "assign uint = {1'h0, a} + {1'h0, b};"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := io.a + io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("-"):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "assign uint = {1'h0, a} - {1'h0, b};"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := io.a - io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("*"):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "assign uint = {1'h0, a} * {1'h0, b};"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := (io.a * io.b).asBits.bits(p.width, 0).asUInt
        io.bool.dontCare()
        io.bits.dontCare()
    test("/"):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "assign uint = {1'h0, a / b};"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := io.a / io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("%"):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "assign uint = {1'h0, a % b};"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := io.a % io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("<"):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "assign bool = a < b;"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint.dontCare()
        io.bool := io.a < io.b
        io.bits.dontCare()
    test("<="):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "assign bool = a <= b;"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint.dontCare()
        io.bool := io.a <= io.b
        io.bits.dontCare()
    test(">"):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "assign bool = a > b;"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint.dontCare()
        io.bool := io.a > io.b
        io.bits.dontCare()
    test(">="):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "assign bool = a >= b;"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint.dontCare()
        io.bool := io.a >= io.b
        io.bits.dontCare()
    test("==="):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "assign bool = a == b;"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint.dontCare()
        io.bool := io.a === io.b
        io.bits.dontCare()
    test("=/="):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "assign bool = a != b;"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint.dontCare()
        io.bool := io.a =/= io.b
        io.bits.dontCare()
    test("<< int"):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "assign uint = {a[6:0], 2'h0};"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := (io.a << 2).asBits.bits(p.width, 0).asUInt
        io.bool.dontCare()
        io.bits.dontCare()
    test("<< uint"):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "wire [262:0] tests = {255'h0, a} << b;",
        "assign uint = tests[8:0];"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := (io.a << io.b).asBits.bits(p.width, 0).asUInt
        io.bool.dontCare()
        io.bits.dontCare()
    test(">> int"):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "assign uint = {5'h0, a[7:4]};"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := io.a >> 4
        io.bool.dontCare()
        io.bits.dontCare()
    test(">> uint"):
      verilogTest(parameter, UIntSpecInterface(parameter))(
        "assign uint = {1'h0, a >> b};"
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := io.a >> io.b
        io.bool.dontCare()
        io.bits.dontCare()
