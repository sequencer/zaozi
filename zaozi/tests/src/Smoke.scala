// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.{*, given}
import utest.*

case class SimpleParameter(width: Int) extends Parameter

class PassthroughInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter) {
  val i = Flipped(UInt(parameter.width.W))
  val o = Aligned(UInt(parameter.width.W))
}

class AsyncDomain extends Bundle:
  val clock = Aligned(Clock())
  val reset = Aligned(AsyncReset())

class SyncDomain extends Bundle:
  val clock = Aligned(Clock())
  val reset = Aligned(AsyncReset())

class RegisterInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter) {
  val asyncDomain = Flipped(new AsyncDomain)
  val syncDomain  = Flipped(new SyncDomain)
  val passthrough = Aligned(new PassthroughInterface(parameter))
}

object Smoke extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(32)
    val out       = new StringBuilder
    test("Passthrough"):
      firrtlTest(parameter, PassthroughInterface(parameter))("wire io : { i : UInt<32>, flip o : UInt<32> }"):
        (p, io) => io.o := io.i
    test("Referable"):
      test("Register"):
        val interface = new RegisterInterface(parameter)
        firrtlTest(parameter, interface)(
          "reg regWithoutInit : UInt<32>, io.syncDomain.clock",
          "regreset asyncRegWithInit : UInt<32>, io.asyncDomain.clock,\n      io.asyncDomain.reset, UInt<32>(0)",
          "regreset syncRegWithInit : UInt<32>, io.syncDomain.clock,\n      io.syncDomain.reset, UInt<32>(0)"
        ): (p, io) =>
          val regWithoutInit:   Referable[UInt] =
            Reg(
              tpe = UInt(32.W),
              clock = io.syncDomain.clock
            )
          val asyncRegWithInit: Referable[UInt] =
            RegInit(
              tpe = UInt(32.W),
              clock = io.asyncDomain.clock,
              reset = io.asyncDomain.reset,
              init = 0.U(32.W)
            )
          val syncRegWithInit:  Referable[UInt] =
            RegInit(
              tpe = UInt(32.W),
              clock = io.syncDomain.clock,
              reset = io.syncDomain.reset,
              init = 0.U(32.W)
            )
          io.passthrough.o := regWithoutInit
          regWithoutInit   := asyncRegWithInit
          asyncRegWithInit := syncRegWithInit
          syncRegWithInit  := io.passthrough.i
      test("Instance"):
        firrtlTest(parameter, new PassthroughInterface(parameter))(
          "inst passthroughInstance0 of Passthrough",
          "wire passthroughInstance0_io : { flip i : UInt<32>, o : UInt<32> }",
          "inst passthroughInstance1 of Passthrough",
          "wire passthroughInstance1_io : { flip i : UInt<32>, o : UInt<32> }",
          "connect io.o, passthroughInstance0_io.o",
          "connect passthroughInstance0_io.i, passthroughInstance1_io.o",
          "connect passthroughInstance1_io.i, io.i"
        ): (p, io) =>
          val interface = new PassthroughInterface(parameter)
          val passthroughInstance0: Instance[PassthroughInterface] = Instance("Passthrough", interface)
          val passthroughInstance1: Instance[PassthroughInterface] = Instance("Passthrough", interface)
          io.o                   := passthroughInstance0.o
          passthroughInstance0.i := passthroughInstance1.o
          passthroughInstance1.i := io.i
