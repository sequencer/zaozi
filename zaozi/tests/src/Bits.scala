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
          io.field("bits")
            .asInstanceOf[Ref[Bits]] :=
            io.field("a").asInstanceOf[Ref[Bits]].asBits
      test("AsUInt"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.uint, asUInt(io.a)"
        ): (p, io) =>
          io.field("uint")
            .asInstanceOf[Ref[UInt]] :=
            io.field("a").asInstanceOf[Ref[Bits]].asUInt
      test("AsSInt"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.sint, asSInt(io.a)"
        ): (p, io) =>
          io.field("sint").asInstanceOf[Ref[SInt]] :=
            io.field("a").asInstanceOf[Ref[Bits]].asSInt
      test("Not"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, not(io.a)"
        ): (p, io) =>
          io.field("bits").asInstanceOf[Ref[Bits]] :=
            ~io.field("a").asInstanceOf[Ref[Bits]]
      test("AndR"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bool, andr(io.a)"
        ): (p, io) =>
          io.field("bool").asInstanceOf[Ref[Bool]] :=
            io.field("a").asInstanceOf[Ref[Bits]].andR
      test("OrR"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bool, orr(io.a)"
        ): (p, io) =>
          io.field("bool").asInstanceOf[Ref[Bool]] :=
            io.field("a").asInstanceOf[Ref[Bits]].orR
      test("Eq"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bool, eq(io.a, io.b)"
        ): (p, io) =>
          io.field("bool").asInstanceOf[Ref[Bool]] :=
            io.field("a").asInstanceOf[Ref[Bits]] === io.field("b").asInstanceOf[Ref[Bits]]
      test("Neq"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bool, neq(io.a, io.b)"
        ): (p, io) =>
          io.field("bool").asInstanceOf[Ref[Bool]] :=
            io.field("a").asInstanceOf[Ref[Bits]] =/= io.field("b").asInstanceOf[Ref[Bits]]
      test("Dshl"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, dshl(io.a, io.c)"
        ): (p, io) =>
          io.field("bits").asInstanceOf[Ref[Bits]] :=
            io.field("a").asInstanceOf[Ref[Bits]] <<< io.field("c").asInstanceOf[Ref[UInt]]
      test("Dshr"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, dshr(io.a, io.c)"
        ): (p, io) =>
          io.field("bits").asInstanceOf[Ref[Bits]] :=
            io.field("a").asInstanceOf[Ref[Bits]] >>> io.field("c").asInstanceOf[Ref[UInt]]
      test("And"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, and(io.a, io.b)"
        ): (p, io) =>
          io.field("bits").asInstanceOf[Ref[Bits]] :=
            io.field("a").asInstanceOf[Ref[Bits]] & io.field("b").asInstanceOf[Ref[Bits]]
      test("Or"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, or(io.a, io.b)"
        ): (p, io) =>
          io.field("bits").asInstanceOf[Ref[Bits]] :=
            io.field("a").asInstanceOf[Ref[Bits]] | io.field("b").asInstanceOf[Ref[Bits]]
      test("Xor"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, xor(io.a, io.b)"
        ): (p, io) =>
          io.field("bits").asInstanceOf[Ref[Bits]] :=
            io.field("a").asInstanceOf[Ref[Bits]] ^ io.field("b").asInstanceOf[Ref[Bits]]
      test("Cat"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, cat(io.a, io.b)"
        ): (p, io) =>
          io.field("bits").asInstanceOf[Ref[Bits]] :=
            io.field("a").asInstanceOf[Ref[Bits]] ## io.field("b").asInstanceOf[Ref[Bits]]
      test("Shl"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, shl(io.a, 2)"
        ): (p, io) =>
          io.field("bits").asInstanceOf[Ref[Bits]] :=
            io.field("a").asInstanceOf[Ref[Bits]] << 2
      test("Shr"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, shr(io.a, 2)"
        ): (p, io) =>
          io.field("bits").asInstanceOf[Ref[Bits]] :=
            io.field("a").asInstanceOf[Ref[Bits]] >> 2
      test("Head"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, head(io.a, 2)"
        ): (p, io) =>
          io.field("bits").asInstanceOf[Ref[Bits]] :=
            io.field("a").asInstanceOf[Ref[Bits]].head(2)
      test("Tail"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, tail(io.a, 2)"
        ): (p, io) =>
          io.field("bits").asInstanceOf[Ref[Bits]] :=
            io.field("a").asInstanceOf[Ref[Bits]].tail(2)
      test("Pad"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, pad(io.a, 32)"
        ): (p, io) =>
          io.field("bits").asInstanceOf[Ref[Bits]] :=
            io.field("a").asInstanceOf[Ref[Bits]].pad(32)
      test("Bits"):
        firrtlTest(parameter, new BitsSpecInterface(parameter))(
          "connect io.bits, bits(io.a, 4, 2)"
        ): (p, io) =>
          io.field("bits").asInstanceOf[Ref[Bits]] :=
            io.field("a").asInstanceOf[Ref[Bits]].extract(4, 2)
