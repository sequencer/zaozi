// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.{*, given}
import utest.*

class BitsSpecInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter) {
  val a          = Flipped(Bits(parameter.width.W))
  val b          = Flipped(Bits(parameter.width.W))
  val c          = Flipped(UInt(parameter.width.W))
  val uint       = Aligned(UInt(parameter.width.W))
  val sint       = Aligned(SInt(parameter.width.W))
  val bits       = Aligned(Bits(parameter.width.W))
  val bool       = Aligned(Bool())
  val clock      = Aligned(Clock())
  val asyncReset = Aligned(AsyncReset())
}

object BitsSpec extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(8)
    val out       = new StringBuilder
    test("Bits"):
      test("AsBits"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, asUInt(io.a)"
        ): (p, io) =>
          io.field[Bits]("bits") := io.field[Bits]("a").asBits
      test("AsUInt"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.uint, asUInt(io.a)"
        ): (p, io) =>
          io.field[UInt]("uint") := io.field[Bits]("a").asUInt
      test("AsSInt"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.sint, asSInt(io.a)"
        ): (p, io) =>
          io.field[SInt]("sint") := io.field[Bits]("a").asSInt
      test("Not"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, not(io.a)"
        ): (p, io) =>
          io.field[Bits]("bits") := ~io.field[Bits]("a")
      test("AndR"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bool, andr(io.a)"
        ): (p, io) =>
          io.field[Bool]("bool") := io.field[Bits]("a").andR
      test("OrR"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bool, orr(io.a)"
        ): (p, io) =>
          io.field[Bool]("bool") := io.field[Bits]("a").orR
      test("Eq"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bool, eq(io.a, io.b)"
        ): (p, io) =>
          io.field[Bool]("bool") := io.field[Bits]("a") === io.field[Bits]("b")
      test("Neq"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bool, neq(io.a, io.b)"
        ): (p, io) =>
          io.field[Bool]("bool") := io.field[Bits]("a") =/= io.field[Bits]("b")
      test("Dshl"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, dshl(io.a, io.c)"
        ): (p, io) =>
          io.field[Bits]("bits") := io.field[Bits]("a") <<< io.field[UInt]("c")
      test("Dshr"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, dshr(io.a, io.c)"
        ): (p, io) =>
          io.field[Bits]("bits") := io.field[Bits]("a") >>> io.field[UInt]("c")
      test("And"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, and(io.a, io.b)"
        ): (p, io) =>
          io.field[Bits]("bits") := io.field[Bits]("a") & io.field[Bits]("b")
      test("Or"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, or(io.a, io.b)"
        ): (p, io) =>
          io.field[Bits]("bits") := io.field[Bits]("a") | io.field[Bits]("b")
      test("Xor"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, xor(io.a, io.b)"
        ): (p, io) =>
          io.field[Bits]("bits") := io.field[Bits]("a") ^ io.field[Bits]("b")
      test("Cat"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, cat(io.a, io.b)"
        ): (p, io) =>
          io.field[Bits]("bits") := io.field[Bits]("a") ## io.field[Bits]("b")
      test("Shl"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, shl(io.a, 2)"
        ): (p, io) =>
          io.field[Bits]("bits") := io.field[Bits]("a") << 2
      test("Shr"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, shr(io.a, 2)"
        ): (p, io) =>
          io.field[Bits]("bits") := io.field[Bits]("a") >> 2
      test("Head"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, head(io.a, 2)"
        ): (p, io) =>
          io.field[Bits]("bits") := io.field[Bits]("a").head(2)
      test("Tail"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, tail(io.a, 2)"
        ): (p, io) =>
          io.field[Bits]("bits") := io.field[Bits]("a").tail(2)
      test("Pad"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, pad(io.a, 32)"
        ): (p, io) =>
          io.field[Bits]("bits") := io.field[Bits]("a").pad(32)
      test("Bits"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, bits(io.a, 4, 2)"
        ): (p, io) =>
          io.field[Bits]("bits") := io.field[Bits]("a").extract(4, 2)