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
  val i = Flipped("i", UInt(parameter.width.W))
  val o = Aligned("o", UInt(parameter.width.W))
}

class RegisterInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter) {
  val asyncDomain = Flipped(
    "asyncDomain",
    new Bundle {
      val clk: Unit = Aligned("clock", Clock())
      val reset = Aligned("reset", AsyncReset())
    }
  )
  val syncDomain  = Flipped(
    "syncDomain",
    new Bundle {
      val clk   = Aligned("clock", Clock())
      val reset = Aligned("reset", Reset())
    }
  )
  val passthough  = Aligned("passthrough", new PassthroughInterface(parameter))
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
          """    reg myReg : UInt<32>, io.syncDomain.clock
            |    regreset myAsyncReg : UInt<32>, io.asyncDomain.clock, io.asyncDomain.reset,
            |      UInt<32>(0)
            |    regreset mySyncReg : UInt<32>, io.syncDomain.clock, io.syncDomain.reset,
            |      UInt<32>(0)
            |    connect io.passthrough.o, myReg
            |    connect myReg, myAsyncReg
            |    connect myAsyncReg, mySyncReg
            |    connect mySyncReg, io.passthrough.i
            |""".stripMargin
        ): (p, io) =>
          val regWithoutInit:   Referable[UInt] =
            Reg(
              name = "myReg",
              tpe = UInt(32.W),
              clock = io.field("syncDomain").asInstanceOf[Ref[Bundle]].field("clock").asInstanceOf[Ref[Clock]]
            )
          val asyncRegWithInit: Referable[UInt] =
            RegInit(
              name = "myAsyncReg",
              tpe = UInt(32.W),
              clock = io.field("asyncDomain").asInstanceOf[Ref[Bundle]].field("clock").asInstanceOf[Ref[Clock]],
              reset = io.field("asyncDomain").asInstanceOf[Ref[Bundle]].field("reset").asInstanceOf[Ref[AsyncReset]],
              init = 0.U(32.W)
            )
          val syncRegWithInit:  Referable[UInt] =
            RegInit(
              name = "mySyncReg",
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
          "inst i0 of Passthrough",
          "wire i0_io : { flip i : UInt<32>, o : UInt<32> }",
          "inst i1 of Passthrough",
          "wire i1_io : { flip i : UInt<32>, o : UInt<32> }",
          "connect io.o, i0_io.o",
          "connect i0_io.i, i1_io.o",
          "connect i1_io.i, io.i"
        ): (p, io) =>
          val interface = new PassthroughInterface(parameter)
          val passthroughInstance0: Instance[PassthroughInterface] = Instance("i0", "Passthrough", interface)
          val passthroughInstance1: Instance[PassthroughInterface] = Instance("i1", "Passthrough", interface)
          io.field("o")                   := passthroughInstance0.field("o")
          passthroughInstance0.field("i") := passthroughInstance1.field("o")
          passthroughInstance1.field("i") := io.field("i")
