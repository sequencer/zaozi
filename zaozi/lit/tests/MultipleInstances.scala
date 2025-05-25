// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 <liu@jiuyang.me>

// DEFINE: %{test} = scala-cli --server=false --java-home=%JAVAHOME --extra-jars=%RUNCLASSPATH --scala-version=%SCALAVERSION -O="-experimental" --java-opt="--enable-native-access=ALL-UNNAMED" --java-opt="--enable-preview" --java-opt="-Djava.library.path=%JAVALIBRARYPATH" --main-class GCD %s --
// RUN: %{test} config %t.json --width 32 --use-async-reset false
// RUN: %{test} design %t.json
// RUN: firtool GCD*.mlirbc | FileCheck %s -check-prefix=GCD
// RUN: firtool Subtractor*.mlirbc | FileCheck %s -check-prefix=SUB
// RUN: rm %t.json *.mlirbc -f

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.magic.macros.generator
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

import org.llvm.mlir.scalalib.capi.ir.{Block, Context, Module as MlirModule}

import java.lang.foreign.Arena
import mainargs.TokensReader

trait HasFire[T <: Bundle, R <: Referable[T]]:
  extension (ref: R)
    def fire(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name.Machine,
      instCtx:   InstanceContext
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
      valName:   sourcecode.Name.Machine,
      instCtx:   InstanceContext
    )(
      using Arena,
      Block
    ): Node[Bool] = ref.valid & ref.ready

object Valid:
  def apply[T <: Data](bits: T): ValidIO[T] = new ValidIO[T](bits)

class ValidIO[T <: Data](_bits: T) extends Bundle:
  val valid: BundleField[Bool] = Aligned(Bool())
  val bits:  BundleField[T]    = Aligned(_bits)

case class GCDParameter(width: Int, useAsyncReset: Boolean) extends Parameter
given upickle.default.ReadWriter[GCDParameter] = upickle.default.macroRW

class GCDLayers(parameter: GCDParameter) extends LayerInterface(parameter)

class GCDInput(parameter: GCDParameter) extends Bundle:
  val x: BundleField[UInt] = Aligned(UInt(parameter.width.W))
  val y: BundleField[UInt] = Aligned(UInt(parameter.width.W))

class GCDOutput(parameter: GCDParameter) extends Bundle:
  val z: BundleField[UInt] = Aligned(UInt(parameter.width.W))

class GCDIO(parameter: GCDParameter) extends HWInterface(parameter):
  val clock:  BundleField[Clock]                 = Flipped(Clock())
  val reset:  BundleField[Reset]                 = Flipped(if (parameter.useAsyncReset) AsyncReset() else Reset())
  val input:  BundleField[DecoupledIO[GCDInput]] = Flipped(Decoupled(new GCDInput(parameter)))
  val output: BundleField[ValidIO[GCDOutput]]    = Aligned(Valid(GCDOutput(parameter)))

class GCDProbe(parameter: GCDParameter) extends DVInterface[GCDParameter, GCDLayers](parameter)

case class SubtractorParameter(width: Int) extends Parameter
given upickle.default.ReadWriter[SubtractorParameter] = upickle.default.macroRW

class SubtractorLayers(parameter: SubtractorParameter) extends LayerInterface(parameter)

class SubtractorIO(
  parameter: SubtractorParameter)
    extends HWInterface(parameter):
  val a = Flipped(UInt(parameter.width.W))
  val b = Flipped(UInt(parameter.width.W))
  val z = Aligned(UInt(parameter.width.W))

class SubtractorProbe(parameter: SubtractorParameter)
    extends DVInterface[SubtractorParameter, SubtractorLayers](parameter)

// SUB:      module Subtractor_f34dfd42(
// SUB-NEXT:   input [31:0] a,
// SUB-NEXT:   b,
// SUB-NEXT:   output [31:0] z
// SUB-NEXT: );
@generator
object Subtractor extends Generator[SubtractorParameter, SubtractorLayers, SubtractorIO, SubtractorProbe]:
  def architecture(parameter: SubtractorParameter) =
    val io = summon[Interface[SubtractorIO]]
    io.z := (io.a - io.b).asBits.tail(parameter.width).asUInt

// GCD:      module GCD_35bf2066(
// GCD-NEXT:   output        output_valid,
// GCD-NEXT:   output [31:0] output_bits_z,
// GCD-NEXT:   input         input_valid,
// GCD-NEXT:   output        input_ready,
// GCD-NEXT:   input  [31:0] input_bits_x,
// GCD-NEXT:                 input_bits_y,
// GCD-NEXT:   input         reset,
// GCD-NEXT:                 clock
// GCD-NEXT: );
@generator
object GCD extends Generator[GCDParameter, GCDLayers, GCDIO, GCDProbe]:
  def architecture(parameter: GCDParameter) =
    val io           = summon[Interface[GCDIO]]
    given Ref[Clock] = io.clock
    given Ref[Reset] = io.reset

    val x:           Referable[UInt] = Reg(UInt(parameter.width.W))
    val y:           Referable[UInt] = RegInit(0.U(parameter.width.W))
    val startupFlag: Referable[Bool] = RegInit(false.B)
    val busy:        Referable[Bool] = y =/= 0.U

    io.input.ready   := !busy
    io.output.bits.z := x
    io.output.valid  := !busy & startupFlag

    // GCD:      Subtractor_f34dfd42 sub1 (
    // GCD-NEXT:   .a (x),
    // GCD-NEXT:   .b (y),
    // GCD-NEXT:   .z (_sub1_z)
    // GCD-NEXT: );
    val sub1 = Subtractor.instantiate(SubtractorParameter(parameter.width))
    sub1.io.a := x
    sub1.io.b := y

    // GCD:      Subtractor_f34dfd42 sub2 (
    // GCD-NEXT:   .a (y),
    // GCD-NEXT:   .b (x),
    // GCD-NEXT:   .z (_sub2_z)
    // GCD-NEXT: );
    val sub2 = Subtractor.instantiate(SubtractorParameter(parameter.width))
    sub2.io.a := y
    sub2.io.b := x

    x := io.input.fire ? (
      io.input.bits.x,
      (x > y) ? (
        sub1.io.z,
        x
      )
    )

    y := io.input.fire ? (
      io.input.bits.y,
      (x > y) ? (
        y,
        sub2.io.z
      )
    )

    startupFlag := io.input.fire ? (
      true.B,
      startupFlag
    )
