// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.{*, given}
import utest.*

class SimpleBundle extends Bundle:
  val g = Aligned(UInt(32.W))

class DynamicBundleInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter):
  val a = Aligned(UInt(32.W))
  val b = Flipped(UInt(32.W))
  val c = Aligned(new Bundle {
    val d = Aligned(UInt(32.W))
  })
  val f = Flipped(new SimpleBundle)
  val h = Flipped("hhh", UInt(32.W))
  val e = UInt(32.W)
  val i = 32

object BundleSpec extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(8)
    test("Reflect"):
      test("Subaccess on non-Bundle type"):
        Module("NoName", parameter, new DynamicBundleInterface(parameter)): (p, io) =>
          compileError("""io.a.a""").check(
            "",
            "Type parameter T must be a subtype of DynamicSubfield, but got me.jiuyang.zaozi.UInt."
          )
      test("Symbol not found"):
        Module("NoName", parameter, new DynamicBundleInterface(parameter)): (p, io) =>
          compileError("""io.fourzerofour""").check(
            "",
            "Field 'fourzerofour' does not exist in type me.jiuyang.zaozi.tests.DynamicBundleInterface."
          )
      test("Access non Data type"):
        test("Int"):
          Module("NoName", parameter, new DynamicBundleInterface(parameter)): (p, io) =>
            compileError("""io.i""").check(
              "",
              "Field type 'scala.Int' does not conform to the upper bound BundleField."
            )
        test("UInt"):
          Module("NoName", parameter, new DynamicBundleInterface(parameter)): (p, io) =>
            compileError("""io.e""").check(
              "",
              "Field type 'me.jiuyang.zaozi.UInt' does not conform to the upper bound BundleField."
            )
      test("Bundle in Bundle"):
        test("Structural Type doesn't work"):
          Module("NoName", parameter, new DynamicBundleInterface(parameter)): (p, io) =>
            compileError("""io.c.d""").check(
              "",
              "Field 'd' does not exist in type me.jiuyang.zaozi.Bundle."
            )
        test("Bundle in Bundle should work"):
          firrtlTest(parameter, new DynamicBundleInterface(parameter))(
            "connect io.a, io.f.g"
          ): (p, io) =>
            io.a := io.f.g
      test("Custom val name"):
        firrtlTest(parameter, new DynamicBundleInterface(parameter))(
          "connect io.a, io.hhh"
        ): (p, io) =>
          io.a := io.h
      test("Symbol found"):
        firrtlTest(parameter, new DynamicBundleInterface(parameter))(
          "connect io.a, io.b"
        ): (p, io) =>
          io.a := io.b