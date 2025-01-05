// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.circt.scalalib.firrtl.capi.{FirtoolOptions, FirtoolOptionsApi, given_DialectHandleApi, given_FirtoolOptionsApi, given_PassManagerApi}
import org.llvm.mlir.scalalib.{Block, Context, ContextApi, PassManager, PassManagerApi, given_ContextApi, given_PassManagerApi}
import utest.*

import java.lang.foreign.Arena

case class GCDParameter(width: Int, useAsyncReset: Boolean) extends Parameter

trait HasFire[T <: Bundle, R <: Referable[T]]:
  extension (ref: R)
    def fire(
              using ctx: Context,
              file:      sourcecode.File,
              line:      sourcecode.Line,
              valName:   sourcecode.Name
            )(using Arena, Block): Node[Bool]

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
            )(using Arena, Block): Node[Bool] = ref.valid & ref.ready

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

class GCDInterface(parameter: GCDParameter) extends Interface[GCDParameter](parameter):
  def moduleName = "GCD"
  val clock:  BundleField[Clock]                 = Flipped(Clock())
  val reset:  BundleField[Reset]    = Flipped(if (parameter.useAsyncReset) AsyncReset() else Reset())
  val input:  BundleField[DecoupledIO[GCDInput]] = Flipped(Decoupled(new GCDInput(parameter)))
  val output: BundleField[ValidIO[GCDOutput]]    = Aligned(Valid(GCDOutput(parameter)))

object GCDSpec extends TestSuite:
  val tests = Tests:
    test("GCD"):
      val parameter = GCDParameter(32, false)
      mlirTest(parameter, new GCDInterface(parameter))(): (p, io) =>
        given Ref[Clock] = io.clock
        given Ref[Reset] = io.reset
        val x:           Referable[UInt] = Reg(UInt(parameter.width.W))
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