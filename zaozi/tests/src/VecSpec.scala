// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozitest

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.Interface
import me.jiuyang.zaozi.testlib.*

import org.llvm.mlir.scalalib.capi.ir.{given_ContextApi, Block, Context, ContextApi}

import java.lang.foreign.Arena
import utest.*
import me.jiuyang.zaozi.magic.macros.generator

case class VecSpecParameter(width: Int, vecCount: Int) extends Parameter
given upickle.default.ReadWriter[VecSpecParameter] = upickle.default.macroRW

class VecSpecLayers(parameter: VecSpecParameter) extends LayerInterface(parameter):
  def layers = Seq.empty

class VecSpecIO(parameter: VecSpecParameter) extends HWBundle(parameter):
  val a   = Flipped(Vec(parameter.vecCount, Bits(parameter.width.W)))
  val idx = Flipped(UInt(BigInt(parameter.vecCount).bitLength.W))
  val b   = Aligned(Vec(parameter.vecCount, Bits(parameter.width.W)))
  val out = Aligned(Bits(parameter.width.W))

class VecSpecProbe(parameter: VecSpecParameter) extends DVBundle[VecSpecParameter, VecSpecLayers](parameter)

object VecSpec extends TestSuite:
  val tests = Tests:
    test("Assign"):
      @generator
      object Assign extends Generator[VecSpecParameter, VecSpecLayers, VecSpecIO, VecSpecProbe] with HasFirrtlTest:
        def architecture(parameter: VecSpecParameter) =
          val io = summon[Interface[VecSpecIO]]
          io.b := io.a
          io.out.dontCare()
      Assign.firrtlTest(VecSpecParameter(8, 4))(
        "connect io.b, io.a"
      )
    test("AsBits"):
      @generator
      object Assign extends Generator[VecSpecParameter, VecSpecLayers, VecSpecIO, VecSpecProbe] with HasVerilogTest:
        def architecture(parameter: VecSpecParameter) =
          val io = summon[Interface[VecSpecIO]]
          io.b := io.a.asBits.asVec(Bits(parameter.width.W))
          io.out.dontCare()
      Assign.verilogTest(VecSpecParameter(8, 4))(
        "assign b_0 = a_0",
        "assign b_1 = a_1",
        "assign b_2 = a_2",
        "assign b_3 = a_3"
      )
    test("Dynamic index"):
      @generator
      object DynamicIndex
          extends Generator[VecSpecParameter, VecSpecLayers, VecSpecIO, VecSpecProbe]
          with HasFirrtlTest:
        def architecture(parameter: VecSpecParameter) =
          val io = summon[Interface[VecSpecIO]]
          io.b.dontCare()
          io.out := io.a.bit(io.idx)
      DynamicIndex.firrtlTest(VecSpecParameter(8, 4))(
        "node _GEN_0 = io.a[io.idx]"
      )

    test("Dynamic index apply"):
      @generator
      object DynamicIndexApply
          extends Generator[VecSpecParameter, VecSpecLayers, VecSpecIO, VecSpecProbe]
          with HasFirrtlTest:
        def architecture(parameter: VecSpecParameter) =
          val io = summon[Interface[VecSpecIO]]
          io.b.dontCare()
          io.out := io.a(io.idx)
      DynamicIndexApply.firrtlTest(VecSpecParameter(8, 4))(
        "node _GEN_0 = io.a[io.idx]"
      )

    test("Static index"):
      @generator
      object StaticIndex extends Generator[VecSpecParameter, VecSpecLayers, VecSpecIO, VecSpecProbe] with HasFirrtlTest:
        def architecture(parameter: VecSpecParameter) =
          val io = summon[Interface[VecSpecIO]]
          io.b.dontCare()
          io.out := io.a.bit(3)
      StaticIndex.firrtlTest(VecSpecParameter(8, 4))(
        "node _GEN_0 = io.a[3]"
      )

    test("Static index apply"):
      @generator
      object StaticIndexApply
          extends Generator[VecSpecParameter, VecSpecLayers, VecSpecIO, VecSpecProbe]
          with HasFirrtlTest:
        def architecture(parameter: VecSpecParameter) =
          val io = summon[Interface[VecSpecIO]]
          io.b.dontCare()
          io.out := io.a(3)
      StaticIndexApply.firrtlTest(VecSpecParameter(8, 4))(
        "node _GEN_0 = io.a[3]"
      )

    test("Named static index apply"):
      @generator
      object NamedStaticIndexApply
          extends Generator[VecSpecParameter, VecSpecLayers, VecSpecIO, VecSpecProbe]
          with HasFirrtlTest:
        def architecture(parameter: VecSpecParameter) =
          val io = summon[Interface[VecSpecIO]]
          io.b.dontCare()
          io.out := io.a(idx = 3)
      NamedStaticIndexApply.firrtlTest(VecSpecParameter(8, 4))(
        "node _GEN_0 = io.a[3]"
      )

    test("Apply with incorrect named argument"):
      @generator
      object IncorrectNamedArgument
          extends Generator[VecSpecParameter, VecSpecLayers, VecSpecIO, VecSpecProbe]
          with HasCompileErrorTest:
        def architecture(parameter: VecSpecParameter) =
          val io = summon[Interface[VecSpecIO]]
          compileError("""io.out := io.a(invalid_name = 3)""").check(
            "",
            "Unexpected named arguments invalid_name"
          )
      IncorrectNamedArgument.compileErrorTest(VecSpecParameter(8, 4))

    test("Apply with incorrect number of arguments"):
      @generator
      object IncorrectNumberOfArguments
          extends Generator[VecSpecParameter, VecSpecLayers, VecSpecIO, VecSpecProbe]
          with HasCompileErrorTest:
        def architecture(parameter: VecSpecParameter) =
          val io = summon[Interface[VecSpecIO]]
          compileError("""io.out := io.a(1, 2)""").check(
            "",
            "Expected 1 args, but got 2"
          )
      IncorrectNumberOfArguments.compileErrorTest(VecSpecParameter(8, 4))
