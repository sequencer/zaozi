// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.{*, given}
import utest.*

class BoolSpecInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter) {
  val a          = Flipped(Bool())
  val b          = Flipped(Bool())
  val c          = Flipped(Bool())
  val bool       = Aligned(Bool())
  val bits       = Aligned(Bits(1.W))
  val clock      = Aligned(Clock())
  val asyncReset = Aligned(AsyncReset())
}

object BoolSpec extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(8)
    val out       = new StringBuilder
    test("Bool"):
      test("AsBits"):
        firrtlTest(parameter, new BoolSpecInterface(parameter))(
          // just type cast in zaozi, not actually firrtl type.
          "connect io.bits, asUInt(io.a)"
        ): (p, io) =>
          io.bits := io.a.asBits
      test("Neg"):
        firrtlTest(parameter, new BoolSpecInterface(parameter))(
          "connect io.bool, neg(io.a)"
        ): (p, io) =>
          io.bool := !io.a
      test("Eq"):
        firrtlTest(parameter, new BoolSpecInterface(parameter))(
          "connect io.bool, eq(io.a, io.b)"
        ): (p, io) =>
          io.bool := io.a === io.b
      test("Neq"):
        firrtlTest(parameter, new BoolSpecInterface(parameter))(
          "connect io.bool, neq(io.a, io.b)"
        ): (p, io) =>
          io.bool := io.a =/= io.b
      test("And"):
        firrtlTest(parameter, new BoolSpecInterface(parameter))(
          "connect io.bool, and(io.a, io.b)"
        ): (p, io) =>
          io.bool := io.a & io.b
      test("Or"):
        firrtlTest(parameter, new BoolSpecInterface(parameter))(
          "connect io.bool, or(io.a, io.b)"
        ): (p, io) =>
          io.bool := io.a | io.b
      test("Xor"):
        firrtlTest(parameter, new BoolSpecInterface(parameter))(
          "connect io.bool, xor(io.a, io.b)"
        ): (p, io) =>
          io.bool := io.a ^ io.b
      test("Mux"):
        firrtlTest(parameter, new BoolSpecInterface(parameter))(
          "connect io.bool, mux(io.c, io.a, io.b)"
        ): (p, io) =>
          io.bool := io.c ? (io.a, io.b)
