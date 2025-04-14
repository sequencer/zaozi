// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.Interface

import org.llvm.circt.scalalib.firrtl.capi.given_DialectHandleApi
import org.llvm.mlir.scalalib.{given_ContextApi, Context, ContextApi}

import java.lang.foreign.Arena
import utest.*

case class VecSpecParameter(width: Int, vecCount: Int) extends Parameter:
  def moduleName: String     = "VecSpecModule"
  def layers:     Seq[Layer] = Nil

class VecSpecIO(
  using VecSpecParameter)
    extends HWInterface[VecSpecParameter]:
  val parameter = summon[VecSpecParameter]
  val a         = Flipped(Vec(parameter.vecCount, Bits(parameter.width.W)))
  val idx       = Flipped(UInt(BigInt(parameter.vecCount).bitLength.W))
  val b         = Aligned(Vec(parameter.vecCount, Bits(parameter.width.W)))
  val out       = Aligned(Bits(parameter.width.W))

class VecSpecProbe(
  using VecSpecParameter)
    extends DVInterface[VecSpecParameter]

object VecSpec extends TestSuite:
  val tests = Tests:
    given VecSpecParameter(8, 4)
    test("Assign"):
      firrtlTest(new VecSpecIO, new VecSpecProbe)(
        "connect io.b, io.a"
      ):
        val io = summon[Interface[VecSpecIO]]
        io.b := io.a
        io.out.dontCare()
    test("Dynamic index"):
      firrtlTest(new VecSpecIO, new VecSpecProbe)(
        "node tests = io.a[io.idx]"
      ):
        val io = summon[Interface[VecSpecIO]]
        io.b.dontCare()
        io.out := io.a.bit(io.idx)
    test("Dynamic index apply"):
      firrtlTest(new VecSpecIO, new VecSpecProbe)(
        "node tests = io.a[io.idx]"
      ):
        val io = summon[Interface[VecSpecIO]]
        io.b.dontCare()
        io.out := io.a(io.idx)
    test("Static index"):
      firrtlTest(new VecSpecIO, new VecSpecProbe)(
        "node tests = io.a[3]"
      ):
        val io = summon[Interface[VecSpecIO]]
        io.b.dontCare()
        io.out := io.a.bit(3)
    test("Static index apply"):
      firrtlTest(new VecSpecIO, new VecSpecProbe)(
        "node tests = io.a[3]"
      ):
        val io = summon[Interface[VecSpecIO]]
        io.b.dontCare()
        io.out := io.a(3)
    test("Named static index apply"):
      firrtlTest(new VecSpecIO, new VecSpecProbe)(
        "node tests = io.a[3]"
      ):
        val io = summon[Interface[VecSpecIO]]
        io.b.dontCare()
        io.out := io.a(idx = 3)

    given Arena   = Arena.ofConfined()
    given Context = summon[ContextApi].contextCreate
    summon[Context].loadFirrtlDialect()
    test("Apply with incorrect named argument"):
      summon[ConstructorApi].Module(new VecSpecIO, new VecSpecProbe):
        val io = summon[Interface[VecSpecIO]]
        compileError("""io.out := io.a(invalid_name = 3)""").check(
          "",
          "missing argument for parameter idx of method vecApplyWrapper in object ApplyHelper"
        )
    test("Apply with incorrect number of arguments"):
      summon[ConstructorApi].Module(new VecSpecIO, new VecSpecProbe):
        val io = summon[Interface[VecSpecIO]]
        compileError("""io.out := io.a(1, 2)""").check(
          "",
          "Expected 1 args, but got 2"
        )
