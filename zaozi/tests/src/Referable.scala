// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.circt.scalalib.firrtl.capi.given_DialectHandleApi
import org.llvm.mlir.scalalib.{Context, ContextApi, given_ContextApi}
import utest.*

import java.lang.foreign.Arena

class AsyncDomain extends Bundle:
  val clock = Aligned(Clock())
  val reset = Aligned(AsyncReset())

class SyncDomain extends Bundle:
  val clock = Aligned(Clock())
  val reset = Aligned(Reset())

class ReferableSpecInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter):
  def moduleName: String = parameter.moduleName
  val asyncDomain = Flipped(new AsyncDomain)
  val syncDomain  = Flipped(new SyncDomain)
  val passthrough = Aligned(new PassthroughInterface(parameter))

object ReferableSpec extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(8, "PassthroughModule")
    test("Instance API"):
      verilogTest(parameter, ReferableSpecInterface(parameter))(
        """%8:3 = "firrtl.instance"() <{moduleName = @M0, name = "inst0", nameKind = #firrtl<name_kind interesting_name>, portDirections = array<i1: false, false, true>, portNames = ["asyncDomain", "syncDomain", "passthrough"]}> : () -> (!firrtl.bundle<reset: asyncreset, clock: clock>, !firrtl.bundle<reset: uint<1>, clock: clock>, !firrtl.bundle<i flip: uint<8>, o: uint<8>>)"""
      ): (p: SimpleParameter, io: Wire[ReferableSpecInterface]) =>
        given Ref[Clock] = io.asyncDomain.clock
        given Ref[Reset] = io.asyncDomain.reset
        val inst0 = Instance(ReferableSpecInterface(p.copy(moduleName = "M0")))
        io.passthrough.o := inst0.io.passthrough.o
        inst0.io.passthrough.i := io.passthrough.i
    test("Wire"):
      mlirTest(parameter, ReferableSpecInterface(parameter))(
        "%wire = firrtl.wire interesting_name : !firrtl.uint<8>"
      ): (p: SimpleParameter, io: Wire[ReferableSpecInterface]) =>
        val wire         = Wire(UInt(parameter.width.W))
        io.passthrough.o := wire
        wire             := io.passthrough.i
    test("Register without reset"):
      mlirTest(parameter, ReferableSpecInterface(parameter))(
        "%4 = firrtl.subfield %3[clock] : !firrtl.bundle<reset: uint<1>, clock: clock>",
        "%reg = firrtl.reg interesting_name %4 : !firrtl.clock, !firrtl.uint<8>"
      ): (p: SimpleParameter, io: Wire[ReferableSpecInterface]) =>
        given Ref[Clock] = io.syncDomain.clock
        val reg          = Reg(UInt(parameter.width.W))
        io.passthrough.o := reg
        reg              := io.passthrough.i
    test("Register with SyncReset"):
      mlirTest(parameter, ReferableSpecInterface(parameter))(
        "%4 = firrtl.subfield %3[clock] : !firrtl.bundle<reset: uint<1>, clock: clock>",
        "%6 = firrtl.subfield %5[reset] : !firrtl.bundle<reset: uint<1>, clock: clock>",
        "%c0_ui8 = firrtl.constant 0 : !firrtl.uint<8>",
        "%reg = firrtl.regreset interesting_name %4, %6, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>"
      ): (p: SimpleParameter, io: Wire[ReferableSpecInterface]) =>
        given Ref[Clock] = io.syncDomain.clock
        given Ref[Reset] = io.syncDomain.reset
        val reg          = RegInit(0.U(8.W))
        io.passthrough.o := reg
        reg              := io.passthrough.i
    test("Register with ASyncReset"):
      mlirTest(parameter, ReferableSpecInterface(parameter))(
        "%4 = firrtl.subfield %3[clock] : !firrtl.bundle<reset: asyncreset, clock: clock>",
        "%6 = firrtl.subfield %5[reset] : !firrtl.bundle<reset: asyncreset, clock: clock>",
        "%c0_ui8 = firrtl.constant 0 : !firrtl.uint<8>",
        "%reg = firrtl.regreset interesting_name %4, %6, %c0_ui8 : !firrtl.clock, !firrtl.asyncreset, !firrtl.uint<8>, !firrtl.uint<8>\n    "
      ): (p: SimpleParameter, io: Wire[ReferableSpecInterface]) =>
        given Ref[Clock] = io.asyncDomain.clock
        given Ref[Reset] = io.asyncDomain.reset
        val reg = RegInit(0.U(8.W))
        io.passthrough.o := reg
        reg              := io.passthrough.i
