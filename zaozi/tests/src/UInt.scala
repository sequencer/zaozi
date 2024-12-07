// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.{*, given}
import utest.*

class UIntSpecInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter) {
  val a          = Flipped(UInt(parameter.width.W))
  val b          = Flipped(UInt(parameter.width.W))
  val c          = Flipped(UInt(parameter.width.W))
  val uint       = Aligned(UInt(parameter.width.W))
  val sint       = Aligned(SInt(parameter.width.W))
  val bits       = Aligned(Bits(parameter.width.W))
  val bool       = Aligned(Bool())
  val clock      = Aligned(Clock())
  val asyncReset = Aligned(AsyncReset())
}

object UIntSpec extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(8)
    val out       = new StringBuilder
    test("UInt"):
      test("AsBits"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          // just type cast in zaozi, not actually firrtl type.
          "connect io.bits, asUInt(io.a)"
        ): (p, io) =>
          io.field[Bits]("bits") := io.field[UInt]("a").asBits
      test("AsUInt"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.uint, asUInt(io.a)"
        ): (p, io) =>
          io.field[UInt]("uint") := io.field[UInt]("a").asUInt
      test("AsSInt"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.sint, asSInt(io.a)"
        ): (p, io) =>
          io.field[SInt]("sint") :=
            io.field[UInt]("a").asSInt
      test("Cvt"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.sint, cvt(io.a)"
        ): (p, io) =>
          io.field[SInt]("sint") := io.field[UInt]("a").zext
      test("Add"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.uint, add(io.a, io.b)"
        ): (p, io) =>
          io.field[UInt]("uint") := io.field[UInt]("a") + io.field[UInt]("b")
      test("Sub"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.uint, sub(io.a, io.b)"
        ): (p, io) =>
          io.field[UInt]("uint") := io.field[UInt]("a") - io.field[UInt]("b")
      test("Mul"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.uint, mul(io.a, io.b)"
        ): (p, io) =>
          io.field[UInt]("uint") := io.field[UInt]("a") * io.field[UInt]("b")
      test("Div"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.uint, div(io.a, io.b)"
        ): (p, io) =>
          io.field[UInt]("uint") := io.field[UInt]("a") / io.field[UInt]("b")
      test("Mod"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.uint, rem(io.a, io.b)"
        ): (p, io) =>
          io.field[UInt]("uint") := io.field[UInt]("a") % io.field[UInt]("b")
      test("Lt"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.bool, lt(io.a, io.b)"
        ): (p, io) =>
          io.field[Bool]("bool") := io.field[UInt]("a") < io.field[UInt]("b")
      test("Leq"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.bool, leq(io.a, io.b)"
        ): (p, io) =>
          io.field[Bool]("bool") := io.field[UInt]("a") <= io.field[UInt]("b")
      test("Gt"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.bool, gt(io.a, io.b)"
        ): (p, io) =>
          io.field[Bool]("bool") := io.field[UInt]("a") > io.field[UInt]("b")
      test("Geq"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.bool, geq(io.a, io.b)"
        ): (p, io) =>
          io.field[Bool]("bool") := io.field[UInt]("a") >= io.field[UInt]("b")
      test("Eq"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.bool, eq(io.a, io.b)"
        ): (p, io) =>
          io.field[Bool]("bool") := io.field[UInt]("a") === io.field[UInt]("b")
      test("Neq"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.bool, neq(io.a, io.b)"
        ): (p, io) =>
          io.field[Bool]("bool") := io.field[UInt]("a") =/= io.field[UInt]("b")
      test("Dshl"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.uint, dshl(io.a, io.b)"
        ): (p, io) =>
          io.field[UInt]("uint") := io.field[UInt]("a") <<< io.field[UInt]("b")
      test("Dshr"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.uint, dshr(io.a, io.b)"
        ): (p, io) =>
          io.field[UInt]("uint") := io.field[UInt]("a") >>> io.field[UInt]("b")
      test("Shl"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.uint, shl(io.a, 2)"
        ): (p, io) =>
          io.field[UInt]("uint") := io.field[UInt]("a") << 2
      test("Shr"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.uint, shr(io.a, 2)"
        ): (p, io) =>
          io.field[UInt]("uint") := io.field[UInt]("a") >> 2
      test("Head"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.uint, head(io.a, 2)"
        ): (p, io) =>
          io.field[UInt]("uint") := io.field[UInt]("a").head(2)
      test("Tail"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.uint, tail(io.a, 2)"
        ): (p, io) =>
          io.field[UInt]("uint") := io.field[UInt]("a").tail(2)
      test("Pad"):
        firrtlTest(parameter, new UIntSpecInterface(parameter))(
          "connect io.uint, pad(io.a, 32)"
        ): (p, io) =>
          io.field[UInt]("uint") := io.field[UInt]("a").pad(32)
