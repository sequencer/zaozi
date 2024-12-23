// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.internal.Context
import me.jiuyang.zaozi.{*, given}
import utest.*

case class GCDParameter(width: Int, useAsyncReset: Boolean) extends Parameter

trait HasFire[T <: Bundle, R <: Referable[T]]:
  extension (ref: R)
    def fire(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
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

class GCDInterface(parameter: GCDParameter) extends Interface[GCDParameter](parameter):
  val clock:  BundleField[Clock]                 = Flipped(Clock())
  val reset:  BundleField[Reset | AsyncReset]    = Flipped(if (parameter.useAsyncReset) AsyncReset() else Reset())
  val input:  BundleField[DecoupledIO[GCDInput]] = Flipped(Decoupled(new GCDInput(parameter)))
  val output: BundleField[ValidIO[GCDOutput]]    = Aligned(Valid(GCDOutput(parameter)))

object GCDSpec extends TestSuite:
  val tests = Tests:
    test("GCD"):
      val parameter = GCDParameter(32, false)
      verilogTest(parameter, new GCDInterface(parameter))(
        "assign output_valid = io_input_ready & startupFlag;",
        "assign output_bits_z = x;"
      ): (p, io) =>
        val x:           Referable[UInt] = Reg(UInt(parameter.width.W), io.clock)
        val y:           Referable[UInt] = RegInit(UInt(parameter.width.W), io.clock, io.reset, 0.U)
        val startupFlag: Referable[Bool] = RegInit(Bool(), io.clock, io.reset, false.B)
        val busy:        Referable[Bool] = y =/= 0.U

        io.input.ready   := !busy
        io.output.bits.z := x
        io.output.valid  := !busy & startupFlag

        x := io.input.fire ? (
          io.input.bits.x,
          (x > y) ? (
            x - y,
            x
          )
        )

        y := io.input.fire ? (
          io.input.bits.y,
          (x > y) ? (
            y,
            y - x
          )
        )

        startupFlag := io.input.fire ? (
          true.B,
          startupFlag
        )