// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.mlir.scalalib.{given_ContextApi, Context, ContextApi}
import utest.*

import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.Block

class AsyncDomain extends Bundle:
  val clock = Aligned(Clock())
  val reset = Aligned(AsyncReset())

class SyncDomain extends Bundle:
  val clock = Aligned(Clock())
  val reset = Aligned(Reset())

case class ReferableSpecParameter(width: Int) extends Parameter
given upickle.default.ReadWriter[ReferableSpecParameter] = upickle.default.macroRW

class ReferableSpecLayers(parameter: ReferableSpecParameter) extends LayerInterface(parameter)

class PassthroughIO(parameter: ReferableSpecParameter) extends HWInterface(parameter):
  val i = Flipped(UInt(parameter.width.W))
  val o = Aligned(UInt(parameter.width.W))

class ReferableSpecIO(parameter: ReferableSpecParameter) extends HWInterface(parameter):
  val asyncDomain = Flipped(new AsyncDomain)
  val syncDomain  = Flipped(new SyncDomain)
  val passthrough = Aligned(new PassthroughIO(parameter))

class ReferableSpecProbe(parameter: ReferableSpecParameter)
    extends DVInterface[ReferableSpecParameter, ReferableSpecLayers](parameter)

object ReferableSpec extends TestSuite:
  val tests = Tests:
    test("Wire"):
      @generator
      object WireTest
          extends Generator[ReferableSpecParameter, ReferableSpecLayers, ReferableSpecIO, ReferableSpecProbe]
          with HasVerilogTest:
        def architecture(parameter: ReferableSpecParameter) =
          val io   = summon[Interface[ReferableSpecIO]]
          val wire = Wire(UInt(parameter.width.W))
          io.passthrough.o := wire
          wire             := io.passthrough.i
      WireTest.verilogTest(ReferableSpecParameter(8))(
        "assign passthrough_o = passthrough_i;"
      )

    test("Register without reset"):
      @generator
      object RegisterWithoutReset
          extends Generator[ReferableSpecParameter, ReferableSpecLayers, ReferableSpecIO, ReferableSpecProbe]
          with HasVerilogTest:
        def architecture(parameter: ReferableSpecParameter) =
          val io           = summon[Interface[ReferableSpecIO]]
          given Ref[Clock] = io.syncDomain.clock
          val reg          = Reg(UInt(parameter.width.W))
          io.passthrough.o := reg
          reg              := io.passthrough.i
      RegisterWithoutReset.verilogTest(ReferableSpecParameter(8))(
        "always @(posedge syncDomain_clock)",
        "reg_0 <= passthrough_i;"
      )

    test("Register with SyncReset"):
      @generator
      object RegisterWithSyncReset
          extends Generator[ReferableSpecParameter, ReferableSpecLayers, ReferableSpecIO, ReferableSpecProbe]
          with HasVerilogTest:
        def architecture(parameter: ReferableSpecParameter) =
          val io           = summon[Interface[ReferableSpecIO]]
          given Ref[Clock] = io.syncDomain.clock
          given Ref[Reset] = io.syncDomain.reset
          val reg          = RegInit(0.U(parameter.width.W))
          io.passthrough.o := reg
          reg              := io.passthrough.i
      RegisterWithSyncReset.verilogTest(ReferableSpecParameter(8))(
        "always @(posedge syncDomain_clock) begin",
        "if (syncDomain_reset)"
      )

    test("Register with ASyncReset"):
      @generator
      object RegisterWithASyncReset
          extends Generator[ReferableSpecParameter, ReferableSpecLayers, ReferableSpecIO, ReferableSpecProbe]
          with HasVerilogTest:
        def architecture(parameter: ReferableSpecParameter) =
          val io           = summon[Interface[ReferableSpecIO]]
          given Ref[Clock] = io.asyncDomain.clock
          given Ref[Reset] = io.asyncDomain.reset
          val reg          = RegInit(0.U(parameter.width.W))
          io.passthrough.o := reg
          reg              := io.passthrough.i
      RegisterWithASyncReset.verilogTest(ReferableSpecParameter(8))(
        "always @(posedge asyncDomain_clock or posedge asyncDomain_reset) begin"
      )
