// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*

import org.llvm.circt.scalalib.firrtl.capi.given_DialectHandleApi
import org.llvm.mlir.scalalib.{given_ContextApi, Context, ContextApi}

import java.lang.foreign.Arena
import utest.*

case class BitsSpecParameter(test: String) extends TestParameter:
  def width: Int = 8
  def moduleName: String = "BitsSpec"
  def layers: Seq[Layer] = Seq.empty
  def tests: Map[String, Seq[String]] =
    Map(
      "AsSInt" -> Seq("assign sint = a;"),
      "AsUInt" -> Seq("assign uint = a;"),
      "~" -> Seq("assign bits = ~a;"),
    )

class BitsSpecIO(
  using BitsSpecParameter)
    extends HWInterface[BitsSpecParameter]:
  val parameter  = summon[BitsSpecParameter]
  val a          = Flipped(Bits(parameter.width.W))
  val b          = Flipped(Bits(parameter.width.W))
  val c          = Flipped(UInt(parameter.width.W))
  val d          = Flipped(Bool())
  val sint       = Aligned(SInt((parameter.width).W))
  val uint       = Aligned(UInt((parameter.width).W))
  val bits       = Aligned(Bits(parameter.width.W))
  val widenBits  = Aligned(Bits((2 * parameter.width).W))
  val bool       = Aligned(Bool())
  val clock      = Flipped(Clock())
  val asyncReset = Flipped(AsyncReset())

class BitsSpecProbe(
  using BitsSpecParameter)
    extends DVInterface[BitsSpecParameter]

class BitsSpecTestGenerator(using BitsSpecParameter) extends TestGenerator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe]:
  def hwInterface = new BitsSpecIO
  def probeInterface = new BitsSpecProbe
  def architecture =
    val io = summon[Interface[BitsSpecIO]]
    io.sint.dontCare()
    io.uint.dontCare()
    io.bool.dontCare()
    io.bits.dontCare()
    io.widenBits.dontCare()
    parameter.test match
      case "AsSInt" => io.sint := io.a.asSInt
      case "AsUInt" => io.uint := io.a.asUInt
      case "~" => io.bits := ~io.a

object BitsSpec extends TestSuite:
  val tests = Tests:
    test("AsSInt"):
      given BitsSpecParameter("AsSInt")
      given BitsSpecTestGenerator
      verilogTest
    test("AsUInt"):
      given BitsSpecParameter("AsUInt")
      given BitsSpecTestGenerator
      verilogTest
    test("~"):
      given BitsSpecParameter("~")
      given BitsSpecTestGenerator
      verilogTest