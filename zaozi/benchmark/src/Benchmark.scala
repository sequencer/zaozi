// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.benchmark

import java.util.concurrent.TimeUnit
import org.openjdk.jmh.annotations.*
import org.openjdk.jmh.infra.Blackhole

import me.jiuyang.zaozi.tests.{*, given}
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
import org.llvm.mlir.scalalib.{
  given_ContextApi,
  given_PassManagerApi,
  Block,
  Context,
  ContextApi,
  PassManager,
  PassManagerApi
}
import utest.*

import java.lang.foreign.Arena

// Run with:
// mill zaozi.benchmark.runJmh
class ZaoziBenchmark {

  // This is just an example, copy-paste and modify as appropriate
  // Typically 10 iterations for both warmup and measurement is better
  @Benchmark
  @Warmup(iterations = 3)
  @Measurement(iterations = 3)
  @Fork(value = 1)
  @Threads(value = 1)
  def ZaoziGCDTest(blackHole: Blackhole): Unit =
    given GCDParameter(32, false, "GCD", Seq.empty)
    verilogTest(new GCDIO, new GCDProbe)(
      "module GCD("
    ):
      val p            = summon[GCDParameter]
      val io           = summon[Interface[GCDIO]]
      given Ref[Clock] = io.clock

      given Ref[Reset] = io.reset

      val x:           Referable[UInt] = Reg(UInt(p.width.W))
      val y:           Referable[UInt] = RegInit(0.U(32.W))
      val startupFlag: Referable[Bool] = RegInit(false.B)
      val busy:        Referable[Bool] = y =/= 0.U

      io.input.ready   := !busy
      io.output.bits.z := x
      io.output.valid  := !busy & startupFlag

      val a = x - y

      x := io.input.fire ? (
        io.input.bits.x,
        (x > y) ? (
          (x - y).asBits.tail(32).asUInt,
          x
        )
      )

      y := io.input.fire ? (
        io.input.bits.y,
        (x > y) ? (
          y,
          (y - x).asBits.tail(32).asUInt
        )
      )

      startupFlag := io.input.fire ? (
        true.B,
        startupFlag
      )
}