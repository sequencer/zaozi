// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 <liu@jiuyang.me>
package me.jiuyang.zaozitest

import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import me.jiuyang.zaozi.testlib.*

import org.llvm.mlir.scalalib.capi.ir.{given_ContextApi, Block, Context, ContextApi}
import org.llvm.mlir.scalalib.capi.pass.{given_PassManagerApi, PassManager, PassManagerApi}
import utest.*

import java.lang.foreign.Arena
import scala.annotation.meta.param

case class SVASpecParameter(width: Int) extends Parameter
given upickle.default.ReadWriter[SVASpecParameter] = upickle.default.macroRW

class SVASpecLayers(parameter: SVASpecParameter) extends LayerInterface(parameter):
  def layers = Seq(
    Layer(
      "Assertion"
    )
  )

class SVASpecIO(parameter: SVASpecParameter) extends HWBundle(parameter):
  val iu0 = Flipped(UInt(parameter.width.W))
  val iu1 = Flipped(UInt(parameter.width.W))
  val ib0 = Flipped(Bool())
  val ou0 = Flipped(UInt(parameter.width.W))
  val ou1 = Flipped(UInt(parameter.width.W))

class SVASpecProbe(parameter: SVASpecParameter) extends DVBundle[SVASpecParameter, SVASpecLayers](parameter)

object SVASpec extends TestSuite:
  val tests = Tests:
    test("Simple SVA"):
      @generator
      object SimpleSVA
          extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
          with HasVerilogTest:
        def architecture(parameter: SVASpecParameter) =
          val io    = summon[Interface[SVASpecIO]]
          val probe = summon[Interface[SVASpecProbe]]
          val a: Referable[Bool] & HasOperation = io.ib0
          // macro bug: 
          // [285] [info] compiling 1 Scala source to ./out/zaozi/tests/compile.dest/classes ...
          // [285] [error] -- Error: ./zaozi/tests/src/SVASpec.scala:48:12 ---
          // [285] [error] 48 |          a.S
          // [285] [error]    |          ^^^
          // [285] [error]    |Type parameter T must be a subtype of DynamicSubfield, but got me.jiuyang.zaozi.valuetpe.Bool.
          // [285] [error] one error found
          a.S


      val parameter  = SVASpecParameter(32)
      val moduleName = SimpleSVA.moduleName(parameter)
      SimpleSVA.verilogTest(parameter)(
        s"WTF"
      )
