// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.{*, given}
import utest.*

class SIntSpecInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter) {
  val a          = Flipped(SInt(parameter.width.W))
  val b          = Flipped(SInt(parameter.width.W))
  val c          = Flipped(UInt(parameter.width.W))
  val d          = Flipped(Bool())
  val sint       = Aligned(SInt(parameter.width.W))
  val bits       = Aligned(Bits(parameter.width.W))
  val bool       = Aligned(Bool())
  val clock      = Aligned(Clock())
  val asyncReset = Aligned(AsyncReset())
}

object SIntSpec extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(8)
    val out       = new StringBuilder
    test("SInt"):
      test("AsBits"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.bits, asUInt(io.a)"
        ): (p, io) =>
          io.bits := io.a.asBits
      test("Add"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.sint, add(io.a, io.b)"
        ): (p, io) =>
          io.sint := io.a + io.b
      test("Sub"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.sint, sub(io.a, io.b)"
        ): (p, io) =>
          io.sint := io.a - io.b
      test("Mul"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.sint, mul(io.a, io.b)"
        ): (p, io) =>
          io.sint := io.a * io.b
      test("Div"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.sint, div(io.a, io.b)"
        ): (p, io) =>
          io.sint := io.a / io.b
      test("Mod"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.sint, rem(io.a, io.b)"
        ): (p, io) =>
          io.sint := io.a % io.b
      test("Lt"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.bool, lt(io.a, io.b)"
        ): (p, io) =>
          io.bool := io.a < io.b
      test("Leq"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.bool, leq(io.a, io.b)"
        ): (p, io) =>
          io.bool := io.a <= io.b
      test("Gt"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.bool, gt(io.a, io.b)"
        ): (p, io) =>
          io.bool := io.a > io.b
      test("Geq"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.bool, geq(io.a, io.b)"
        ): (p, io) =>
          io.bool := io.a >= io.b
      test("Eq"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.bool, eq(io.a, io.b)"
        ): (p, io) =>
          io.bool := io.a === io.b
      test("Neq"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.bool, neq(io.a, io.b)"
        ): (p, io) =>
          io.bool := io.a =/= io.b
      test("Dshl"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.sint, dshl(io.a, io.c)"
        ): (p, io) =>
          io.sint := io.a << io.c
      test("Dshr"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.sint, dshr(io.a, io.c)"
        ): (p, io) =>
          io.sint := io.a >> io.c
      test("Shl"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.sint, shl(io.a, 2)"
        ): (p, io) =>
          io.sint := io.a << 2
      test("Shr"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.sint, shr(io.a, 2)"
        ): (p, io) =>
          io.sint := io.a >> 2
      test("Mux"):
        firrtlTest(parameter, new SIntSpecInterface(parameter))(
          "connect io.sint, mux(io.d, io.a, io.b)"
        ): (p, io) =>
          io.sint := io.d ? (io.a, io.b)