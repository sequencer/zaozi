// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.circt.scalalib.firrtl.capi.{FirtoolOptions, FirtoolOptionsApi, given_DialectHandleApi, given_FirtoolOptionsApi, given_PassManagerApi}
import org.llvm.mlir.scalalib.{Context, ContextApi, PassManager, PassManagerApi, given_ContextApi, given_PassManagerApi}
import utest.*

import java.lang.foreign.Arena

class UIntSpecInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter):
  def moduleName: String = parameter.moduleName
  val a = Flipped(UInt(parameter.width.W))
  val b = Flipped(UInt(parameter.width.W))
  val c = Flipped(UInt(parameter.width.W))
  val d = Flipped(Bool())
  val uint = Aligned(UInt((parameter.width + 1).W))
  val bits = Aligned(Bits(parameter.width.W))
  val bool = Aligned(Bool())
  val clock = Flipped(Clock())
  val asyncReset = Flipped(AsyncReset())

object UIntSpec extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(8, "UIntSpecModule")
    val out       = new StringBuilder
    test("asBits"):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint.dontCare()
        io.bool.dontCare()
        io.bits := io.a.asBits
    test("+"):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := io.a + io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("-"):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := io.a - io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("*"):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := io.a - io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("/"):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := io.a - io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("%"):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := io.a - io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test("<"):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint.dontCare()
        io.bool := io.a < io.b
        io.bits.dontCare()
    test("<="):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint.dontCare()
        io.bool := io.a <= io.b
        io.bits.dontCare()
    test(">"):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint.dontCare()
        io.bool := io.a > io.b
        io.bits.dontCare()
    test(">="):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint.dontCare()
        io.bool := io.a >= io.b
        io.bits.dontCare()
    test("==="):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint.dontCare()
        io.bool := io.a === io.b
        io.bits.dontCare()
    test("=/="):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint.dontCare()
        io.bool := io.a =/= io.b
        io.bits.dontCare()
    test("<< int"):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := io.a << 2
        io.bool.dontCare()
        io.bits.dontCare()
    test("<< uint"):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := io.a << io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test(">> int"):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := io.a >> io.b
        io.bool.dontCare()
        io.bits.dontCare()
    test(">> uint"):
      mlirTest(parameter, UIntSpecInterface(parameter))(
      ): (p: SimpleParameter, io: Wire[UIntSpecInterface]) =>
        io.uint := io.a >> io.b
        io.bool.dontCare()
        io.bits.dontCare()
