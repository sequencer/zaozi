// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.smtlib.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.*
import me.jiuyang.smtlib.tpe.*
import me.jiuyang.smtlib.parser.parseZ3Output
import utest.*

import java.lang.foreign.Arena

object Z3Demo extends TestSuite:
  val tests = Tests:
    test("simple Z3 demo"):
      val parsed = smtZ3Test {
        val x = smtValue(Bool)
        smtAssert(x)
      }
      val sat    = parsed.head
      val model  = parsed.tail
      parsed.head ==> ("sat", true)
      parsed.tail ==> Seq(
        ("x", true)
      )
    test("simple Z3 demo with unsat"):
      val parsed = smtZ3Test {
        val x = smtValue(Bool)
        smtAssert(x & !x)
      }
      parsed.head ==> ("unsat", false)
    test("simple Z3 demo with unknown"):
      // reference from: https://stackoverflow.com/questions/66797639/z3py-extremely-slow-with-many-variables
      val parsed = smtZ3Test {
        val x1  = smtValue(SInt)
        val x2  = smtValue(SInt)
        val x3  = smtValue(SInt)
        val x4  = smtValue(SInt)
        val x5  = smtValue(SInt)
        val x6  = smtValue(SInt)
        val x7  = smtValue(SInt)
        val x8  = smtValue(SInt)
        val x9  = smtValue(SInt)
        val x10 = smtValue(SInt)
        val x11 = smtValue(SInt)
        val x12 = smtValue(SInt)
        val x13 = smtValue(SInt)
        val x14 = smtValue(SInt)
        val x15 = smtValue(SInt)
        val x16 = smtValue(SInt)
        smtAssert(
          x1 >= 0.S & x1 <= 10.S
            & x2 >= 0.S & x2 <= 10.S
            & x3 >= 0.S & x3 <= 10.S
            & x4 >= 0.S & x4 <= 10.S
            & x5 >= 0.S & x5 <= 10.S
            & x6 >= 0.S & x6 <= 10.S
            & x7 >= 0.S & x7 <= 10.S
            & x8 >= 0.S & x8 <= 10.S
            & x9 >= 0.S & x9 <= 10.S
            & x10 >= 0.S & x10 <= 10.S
            & x11 >= 0.S & x11 <= 10.S
            & x12 >= 0.S & x12 <= 10.S
            & x13 >= 0.S & x13 <= 10.S
            & x14 >= 0.S & x14 <= 10.S
            & x15 >= 0.S & x15 <= 10.S
            & x16 >= 0.S & x16 <= 10.S
        )
        // format: off
        smtAssert(smtDistinct(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16))
        // format: on
      }
      parsed.head ==> ("unknown", false)
