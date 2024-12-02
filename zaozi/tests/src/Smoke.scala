// SPDX-License-Identifier: Apache-2.0
package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.{*, given}
import utest.*

case class PassthroughParameter(width: Int) extends Parameter

class PassthroughInterface(parameter: PassthroughParameter) extends Interface[PassthroughParameter](parameter) {
  val i = Flipped("i", UInt(parameter.width.W))
  val o = Aligned("o", UInt(parameter.width.W))
}

object Smoke extends TestSuite:
  val tests = Tests:
    test("Passthrough"):
      val parameter = PassthroughParameter(32)
      val interface = new PassthroughInterface(parameter)
      val ctx = Module("Passthrough", parameter, interface) { (p, io) =>
        io.field("o") := io.field("i")
      }
      val out = new StringBuilder
      ctx.handler.mlirExportFIRRTL(ctx.root, out ++= _)
      assert(out.toString.contains("""circuit Passthrough :
                                     |  public module Passthrough :
                                     |    input i : UInt<32>
                                     |    output o : UInt<32>
                                     |
                                     |    wire io : { i : UInt<32>, flip o : UInt<32> }
                                     |    connect io.i, i
                                     |    connect o, io.o
                                     |    connect io.o, io.i
                                     |""".stripMargin))
