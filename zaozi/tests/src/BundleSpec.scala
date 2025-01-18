// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.Interface
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.circt.scalalib.firrtl.capi.given_DialectHandleApi
import org.llvm.mlir.scalalib.{given_ContextApi, Context, ContextApi}
import utest.*

import java.lang.foreign.Arena

class TypeParamIO[A <: Bundle, B <: Bundle](_a: A, _b: B) extends Bundle:
  val a = Flipped(_a)
  val b = Flipped(_b)

class SimpleBundle extends Bundle:
  val g = Aligned(UInt(32.W))

class SimpleBundleA extends Bundle:
  val a = Aligned(UInt(32.W))

class SimpleBundleB extends Bundle:
  val b = Aligned(UInt(32.W))

class BundleSpecIO(parameter: SimpleParameter) extends HWInterface[SimpleParameter](parameter):
  val a = Aligned(UInt(32.W))
  val b = Flipped(UInt(32.W))
  val c = Aligned(new Bundle {
    val d = Aligned(UInt(32.W))
  })
  val f = Flipped(new SimpleBundle)
  val h = Flipped("hhh", UInt(32.W))
  val e = UInt(32.W)
  val i = 32
  val j = Aligned(new TypeParamIO(new SimpleBundleA, new SimpleBundleB))

class BundleSpecProbe(parameter: SimpleParameter) extends DVInterface[SimpleParameter](parameter)

object BundleSpec extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(8, "BundleSpecModule")
    test("Bundle in Bundle should work"):
      firrtlTest(parameter, new BundleSpecIO(parameter), new BundleSpecProbe(parameter))(
        "connect io.a, io.f.g"
      ):
        val io = summon[Interface[BundleSpecIO]]
        io.a := io.f.g
    test("Bundle with type parameter should work"):
      firrtlTest(parameter, new BundleSpecIO(parameter), new BundleSpecProbe(parameter))(
        "connect io.a, io.j.a.a"
      ):
        val io = summon[Interface[BundleSpecIO]]
        io.a := io.j.a.a
    test("Custom val name"):
      firrtlTest(parameter, new BundleSpecIO(parameter), new BundleSpecProbe(parameter))(
        "connect io.a, io.hhh"
      ):
        val io = summon[Interface[BundleSpecIO]]
        io.a := io.h
    test("Symbol found"):
      firrtlTest(parameter, new BundleSpecIO(parameter), new BundleSpecProbe(parameter))(
        "connect io.a, io.b"
      ):
        val io = summon[Interface[BundleSpecIO]]
        io.a := io.b
    test("failures"):
      given Arena   = Arena.ofConfined()
      given Context = summon[ContextApi].contextCreate
      summon[Context].loadFirrtlDialect()
      test("Subaccess on non-Bundle type"):
        summon[ConstructorApi].Module(parameter, new BundleSpecIO(parameter), new BundleSpecProbe(parameter)):
          val io = summon[Interface[BundleSpecIO]]
          compileError("""io.a.a""").check(
            "",
            "Type parameter T must be a subtype of DynamicSubfield, but got me.jiuyang.zaozi.valuetpe.UInt."
          )

      test("Symbol not found"):
        summon[ConstructorApi].Module(parameter, new BundleSpecIO(parameter), new BundleSpecProbe(parameter)):
          val io = summon[Interface[BundleSpecIO]]
          compileError("""io.fourzerofour""").check(
            "",
            "Field 'fourzerofour' does not exist in type me.jiuyang.zaozi.tests.BundleSpecIO."
          )

      test("Access non Data type"):
        test("Int"):
          summon[ConstructorApi].Module(parameter, new BundleSpecIO(parameter), new BundleSpecProbe(parameter)):
            val io = summon[Interface[BundleSpecIO]]
            compileError("""io.i""").check(
              "",
              "Field type 'scala.Int' does not conform to the upper bound BundleField."
            )

        test("UInt"):
          summon[ConstructorApi].Module(parameter, new BundleSpecIO(parameter), new BundleSpecProbe(parameter)):
            val io = summon[Interface[BundleSpecIO]]
            compileError("""io.e""").check(
              "",
              "Field type 'me.jiuyang.zaozi.valuetpe.UInt' does not conform to the upper bound BundleField."
            )

      test("Structural Type doesn't work"):
        summon[ConstructorApi].Module(parameter, new BundleSpecIO(parameter), new BundleSpecProbe(parameter)):
          val io = summon[Interface[BundleSpecIO]]
          compileError("""io.c.d""").check(
            "",
            "Field 'd' does not exist in type me.jiuyang.zaozi.valuetpe.Bundle."
          )
