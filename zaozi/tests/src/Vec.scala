// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.{*, given}
import utest.*

class VecSpecInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter) {
  val a          = Flipped(Vec(4, UInt(parameter.width.W)))
  val b          = Flipped(Vec(4, UInt(parameter.width.W)))
  val c          = Flipped(UInt(parameter.width.W))
  val uint       = Aligned(UInt(parameter.width.W))
  val clock      = Aligned(Clock())
  val asyncReset = Aligned(AsyncReset())
}

object VecSpec extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(8)
    test("Vec"):
      test("StaticAccess"):
        firrtlTest(parameter, new VecSpecInterface(parameter))(
          "connect io.uint, io.a[1]"
        ): (p, io) =>
          io.uint := io.a.idx(1)
      test("DynamicAccess"):
        firrtlTest(parameter, new VecSpecInterface(parameter))(
          "connect io.uint, io.a[io.c]"
        ): (p, io) =>
          io.uint := io.a.idx(io.c)
