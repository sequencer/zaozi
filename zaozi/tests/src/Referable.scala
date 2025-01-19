// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
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

class ReferableSpecIO(
  using SimpleParameter)
    extends HWInterface[SimpleParameter]:
  val parameter   = summon[SimpleParameter]
  val asyncDomain = Flipped(new AsyncDomain)
  val syncDomain  = Flipped(new SyncDomain)
  val passthrough = Aligned(new PassthroughIO)

class ReferableSpecProbe(
  using SimpleParameter)
    extends DVInterface[SimpleParameter]

object ReferableSpec extends TestSuite:
  val tests = Tests:
    given SimpleParameter(8, "PassthroughModule")
    test("Instance API"):
      verilogTest(new ReferableSpecIO, new ReferableSpecProbe)(
        "M0 inst0 ("
      ):
        val p            = summon[SimpleParameter]
        val io           = summon[Interface[ReferableSpecIO]]
        given Ref[Clock] = io.asyncDomain.clock
        given Ref[Reset] = io.asyncDomain.reset
        val inst0 =
          // Actually the Instance should have its own PARAM
          given SimpleParameter(8, "M0")
          Instance(new ReferableSpecIO, new ReferableSpecProbe)
        inst0.io.asyncDomain.clock := io.asyncDomain.clock
        inst0.io.asyncDomain.reset := io.asyncDomain.reset
        inst0.io.syncDomain.clock  := io.syncDomain.clock
        inst0.io.syncDomain.reset  := io.syncDomain.reset
        io.passthrough.o           := inst0.io.passthrough.o
        inst0.io.passthrough.i     := io.passthrough.i
    test("Wire"):
      verilogTest(new ReferableSpecIO, new ReferableSpecProbe)(
        "assign passthrough_o = passthrough_i;"
      ):
        val p    = summon[SimpleParameter]
        val io   = summon[Interface[ReferableSpecIO]]
        val wire = Wire(UInt(p.width.W))
        io.passthrough.o := wire
        wire             := io.passthrough.i
    test("Register without reset"):
      verilogTest(new ReferableSpecIO, new ReferableSpecProbe)(
        "always @(posedge syncDomain_clock)",
        "reg_0 <= passthrough_i;"
      ):
        val p            = summon[SimpleParameter]
        val io           = summon[Interface[ReferableSpecIO]]
        given Ref[Clock] = io.syncDomain.clock
        val reg          = Reg(UInt(p.width.W))
        io.passthrough.o := reg
        reg              := io.passthrough.i
    test("Register with SyncReset"):
      verilogTest(new ReferableSpecIO, new ReferableSpecProbe)(
        "always @(posedge syncDomain_clock) begin",
        "if (syncDomain_reset)"
      ):
        val p            = summon[SimpleParameter]
        val io           = summon[Interface[ReferableSpecIO]]
        given Ref[Clock] = io.syncDomain.clock
        given Ref[Reset] = io.syncDomain.reset
        val reg          = RegInit(0.U(8.W))
        io.passthrough.o := reg
        reg              := io.passthrough.i
    test("Register with ASyncReset"):
      verilogTest(new ReferableSpecIO, new ReferableSpecProbe)(
        "always @(posedge asyncDomain_clock or posedge asyncDomain_reset) begin"
      ):
        val p            = summon[SimpleParameter]
        val io           = summon[Interface[ReferableSpecIO]]
        given Ref[Clock] = io.asyncDomain.clock
        given Ref[Reset] = io.asyncDomain.reset
        val reg          = RegInit(0.U(8.W))
        io.passthrough.o := reg
        reg              := io.passthrough.i
