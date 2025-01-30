// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 <liu@jiuyang.me>
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

case class GCDParameter(width: Int, useAsyncReset: Boolean, moduleName: String, layers: Seq[Layer]) extends Parameter

trait HasFire[T <: Bundle, R <: Referable[T]]:
  extension (ref: R)
    def fire(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    )(
      using Arena,
      Block
    ): Node[Bool]

object Decoupled:
  def apply[T <: Bundle](bits: T) = new DecoupledIO[T](bits)

class DecoupledIO[T <: Bundle](_bits: T) extends Bundle:
  val ready: BundleField[Bool] = Flipped(Bool())
  val valid: BundleField[Bool] = Aligned(Bool())
  val bits:  BundleField[T]    = Aligned(_bits)

given [E <: Bundle, T <: DecoupledIO[E], R <: Referable[T]]: HasFire[T, R] with
  extension (ref: R)
    def fire(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    )(
      using Arena,
      Block
    ): Node[Bool] = ref.valid & ref.ready

object Valid:
  def apply[T <: Data](bits: T): ValidIO[T] = new ValidIO[T](bits)

class ValidIO[T <: Data](_bits: T) extends Bundle:
  val valid: BundleField[Bool] = Aligned(Bool())
  val bits:  BundleField[T]    = Aligned(_bits)

class GCDInput(parameter: GCDParameter) extends Bundle:
  val x: BundleField[UInt] = Aligned(UInt(parameter.width.W))
  val y: BundleField[UInt] = Aligned(UInt(parameter.width.W))

class GCDOutput(parameter: GCDParameter) extends Bundle:
  val z: BundleField[UInt] = Aligned(UInt(parameter.width.W))

class GCDIO(
  using GCDParameter)
    extends HWInterface[GCDParameter]:
  val parameter = summon[GCDParameter]
  val clock:  BundleField[Clock]                 = Flipped(Clock())
  val reset:  BundleField[Reset]                 = Flipped(if (parameter.useAsyncReset) AsyncReset() else Reset())
  val input:  BundleField[DecoupledIO[GCDInput]] = Flipped(Decoupled(new GCDInput(parameter)))
  val output: BundleField[ValidIO[GCDOutput]]    = Aligned(Valid(GCDOutput(parameter)))

class GCDProbe(
  using GCDParameter)
    extends DVInterface[GCDParameter]

// coeffs
case class CoeffsParameter(width: Int, coeffs: Seq[UInt], useAsyncReset: Boolean, moduleName: String, layers: Seq[Layer]) extends Parameter

class CoeffsIO(
  using CoeffsParameter)
    extends HWInterface[CoeffsParameter]:
  val parameter = summon[CoeffsParameter]
  val clock:  BundleField[Clock]                 = Flipped(Clock())
  val reset:  BundleField[Reset]                 = Flipped(if (parameter.useAsyncReset) AsyncReset() else Reset())
  val input:  BundleField[UInt] = Flipped(UInt(parameter.width.W))
  val output: BundleField[UInt]    = Aligned(UInt(parameter.width.W))

class CoeffsProbe(
  using CoeffsParameter)
    extends DVInterface[CoeffsParameter]

object ExportVerilogSpec extends TestSuite:
  val tests = Tests:
    given SimpleParameter(32, "PassthroughModule")
    val out = new StringBuilder
    test("Passthrough"):
      verilogTest(new PassthroughIO, new PassthroughProbe)(
        "assign o = i;"
      ):
        val io = summon[Interface[PassthroughIO]]
        io.o := io.i
    test("GCD"):
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
    test("GCD with When"):
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

        when(x > y) {
          x := (x - y).asBits.tail(32).asUInt
        }.otherwise {
          y := (y - x).asBits.tail(32).asUInt
        }

        when(io.input.fire) {
          x           := io.input.bits.x
          y           := io.input.bits.y
          startupFlag := true.B
        }
        io.input.ready   := !busy
        io.output.bits.z := x
        io.output.valid  := !busy & startupFlag
    test("coeffs"):
      given CoeffsParameter(32, Seq.empty, false, "Coeffs", Seq.empty)
      verilogTest(new CoeffsIO, new CoeffsProbe)(
        "module Coeffs("
      ):
        val p            = summon[CoeffsParameter]
        val io           = summon[Interface[CoeffsIO]]
        given Ref[Clock] = io.clock
        given Ref[Reset] = io.reset

        val zs: Vec[Referable[UInt]] = Vec(p.coeffs.size, Reg(UInt(p.width.W)))
        zs(0) := io.input
        for i <- 1 until p.coeffs.size do
          zs(i) := zs(i - 1)

        val products = p.coeffs.zip(zs).map: 
          (c, z) => (c * z).asBits.bits(p.width, 0).asUInt 

        io.output := products.reduce(_ + _)
