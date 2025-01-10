// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.circt.scalalib.firrtl.capi.given_DialectHandleApi
import org.llvm.mlir.scalalib.{given_ContextApi, Context, ContextApi}
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
        "M0 inst0 ("
      ): (p: SimpleParameter, io: Wire[ReferableSpecInterface]) =>
        given Ref[Clock] = io.asyncDomain.clock
        given Ref[Reset] = io.asyncDomain.reset
        val inst0        = Instance(ReferableSpecInterface(p.copy(moduleName = "M0")))
        inst0.io.asyncDomain.clock := io.asyncDomain.clock
        inst0.io.asyncDomain.reset := io.asyncDomain.reset
        inst0.io.syncDomain.clock  := io.syncDomain.clock
        inst0.io.syncDomain.reset  := io.syncDomain.reset
        io.passthrough.o           := inst0.io.passthrough.o
        inst0.io.passthrough.i     := io.passthrough.i
    test("Wire"):
      verilogTest(parameter, ReferableSpecInterface(parameter))(
        "assign passthrough_o = passthrough_i;"
      ): (p: SimpleParameter, io: Wire[ReferableSpecInterface]) =>
        val wire = Wire(UInt(parameter.width.W))
        io.passthrough.o := wire
        wire             := io.passthrough.i
    test("Register without reset"):
      verilogTest(parameter, ReferableSpecInterface(parameter))(
        "always @(posedge syncDomain_clock)",
        "reg_0 <= passthrough_i;"
      ): (p: SimpleParameter, io: Wire[ReferableSpecInterface]) =>
        given Ref[Clock] = io.syncDomain.clock
        val reg          = Reg(UInt(parameter.width.W))
        io.passthrough.o := reg
        reg              := io.passthrough.i
    test("Register with SyncReset"):
      verilogTest(parameter, ReferableSpecInterface(parameter))(
        "always @(posedge syncDomain_clock) begin",
        "if (syncDomain_reset)"
      ): (p: SimpleParameter, io: Wire[ReferableSpecInterface]) =>
        given Ref[Clock] = io.syncDomain.clock
        given Ref[Reset] = io.syncDomain.reset
        val reg          = RegInit(0.U(8.W))
        io.passthrough.o := reg
        reg              := io.passthrough.i
    test("Register with ASyncReset"):
      verilogTest(parameter, ReferableSpecInterface(parameter))(
        "always @(posedge asyncDomain_clock or posedge asyncDomain_reset) begin"
      ): (p: SimpleParameter, io: Wire[ReferableSpecInterface]) =>
        given Ref[Clock] = io.asyncDomain.clock
        given Ref[Reset] = io.asyncDomain.reset
        val reg          = RegInit(0.U(8.W))
        io.passthrough.o := reg
        reg              := io.passthrough.i
