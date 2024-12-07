// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.{*, given}
import utest.*

import scala.language.dynamics

class DynamicBundleInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter):
  val a = Aligned(UInt(32.W))
  val b = Flipped(UInt(32.W))
  val c = Aligned(new Bundle {
    val d = Aligned(UInt(32.W))
  })
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
            "Type parameter T must be a subtype of Bundle, but got me.jiuyang.zaozi.UInt."
          )
      test("Symbol not found"):
        Module("NoName", parameter, new DynamicBundleInterface(parameter)): (p, io) =>
          compileError("""io.fourzerofour""").check(
            "",
            "Field 'fourzerofour' does not exist in type me.jiuyang.zaozi.tests.DynamicBundleInterface."
          )
      test("Access non Data type"):
        Module("NoName", parameter, new DynamicBundleInterface(parameter)): (p, io) =>
          compileError("""io.i""").check(
            "",
            "Field type 'scala.Int' does not conform to the upper bound Data."
          )
      test("Structural Type doesn't work"):
        Module("NoName", parameter, new DynamicBundleInterface(parameter)): (p, io) =>
          compileError("""io.c.d""").check(
            "",
            "Field 'd' does not exist in type me.jiuyang.zaozi.Bundle."
          )
      test("Symbol found"):
        firrtlTest(parameter, new DynamicBundleInterface(parameter))(
          "connect io.a, io.b"
        ): (p, io) =>
          io.a := io.b
      test("Runtime Error if Aligned or Flipped not found."):
        Module("NoName", parameter, new DynamicBundleInterface(parameter)): (p, io) =>
          assert(
            intercept[Exception](io.e).getMessage ==
              "requirement failed: e not found in a,b,c, did you forget to add Aligned and Flipped?"
          )
