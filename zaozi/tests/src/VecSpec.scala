// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.Interface
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
    test("Vec should work"):
      firrtlTest(new VecSpecIO, new VecSpecProbe)(
        "connect io.b, io.a"
      ):
        val io = summon[Interface[VecSpecIO]]
        io.b := io.a
        io.out.dontCare()
    test("Vec dynamic idx work"):
      firrtlTest(new VecSpecIO, new VecSpecProbe)(
        "node tests = io.a[io.idx]"
      ):
        val io = summon[Interface[VecSpecIO]]
        io.b.dontCare()
        io.out := io.a(io.idx)
    test("Vec static idx work"):
      firrtlTest(new VecSpecIO, new VecSpecProbe)(
        "node tests = io.a[3]"
      ):
        val io = summon[Interface[VecSpecIO]]
        io.b.dontCare()
        io.out := io.a(3)
