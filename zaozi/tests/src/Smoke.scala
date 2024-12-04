// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.{*, given}
import utest.*

def firrtlTest[P <: Parameter](
  parameter:  P,
  interface:  Interface[P],
  moduleName: Option[String] = None
)(checkLines: String*
)(body:       me.jiuyang.zaozi.internal.Context ?=> (P, Wire[Interface[P]]) => Unit
): Unit =
  val out = new StringBuilder
  val ctx = Module(moduleName.getOrElse("NoName"), parameter, interface)(body)
  ctx.handler.mlirExportFIRRTL(ctx.root, out ++= _)
  if (checkLines.isEmpty)
    println(s"please add lines to check for:\n$out")
    assert(false)
  else checkLines.foreach(l => assert(out.toString.contains(l)))

case class SimpleParameter(width: Int) extends Parameter

class PassthroughInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter) {
  val i = Flipped(UInt(parameter.width.W))
  val o = Aligned(UInt(parameter.width.W))
}

class RegisterInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter) {
  val asyncDomain = Flipped(
    new Bundle {
      val clock = Aligned(Clock())
      val reset = Aligned(AsyncReset())
    }
  )
  val syncDomain  = Flipped(
    new Bundle {
      val clock = Aligned(Clock())
      val reset = Aligned(Reset())
    }
  )
  val passthrough  = Aligned(new PassthroughInterface(parameter))
}

object Smoke extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(32)
    val out       = new StringBuilder
    test("Passthrough"):
      firrtlTest(parameter, PassthroughInterface(parameter))("wire io : { i : UInt<32>, flip o : UInt<32> }"):
        (p, io) => io.field("o") := io.field("i")
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
              clock = io.field("syncDomain").asInstanceOf[Ref[Bundle]].field("clock").asInstanceOf[Ref[Clock]]
            )
          val asyncRegWithInit: Referable[UInt] =
            RegInit(
              tpe = UInt(32.W),
              clock = io.field("asyncDomain").asInstanceOf[Ref[Bundle]].field("clock").asInstanceOf[Ref[Clock]],
              reset = io.field("asyncDomain").asInstanceOf[Ref[Bundle]].field("reset").asInstanceOf[Ref[AsyncReset]],
              init = 0.U(32.W)
            )
          val syncRegWithInit:  Referable[UInt] =
            RegInit(
              tpe = UInt(32.W),
              clock = io.field("syncDomain").asInstanceOf[Ref[Bundle]].field("clock").asInstanceOf[Ref[Clock]],
              reset = io.field("syncDomain").asInstanceOf[Ref[Bundle]].field("reset").asInstanceOf[Ref[Reset]],
              init = 0.U(32.W)
            )
          io.field("passthrough").asInstanceOf[Ref[Bundle]].field("o").asInstanceOf[Ref[UInt]] := regWithoutInit
          regWithoutInit                                                                       := asyncRegWithInit
          asyncRegWithInit                                                                     := syncRegWithInit
          syncRegWithInit                                                                      := io.field("passthrough").asInstanceOf[Ref[Bundle]].field("i").asInstanceOf[Ref[UInt]]
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
          io.field("o")                   := passthroughInstance0.field("o")
          passthroughInstance0.field("i") := passthroughInstance1.field("o")
          passthroughInstance1.field("i") := io.field("i")
