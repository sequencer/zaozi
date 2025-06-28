// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvcover.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.tpe.*
import me.jiuyang.rvcover.*

import utest.*

object RecipeTest extends TestSuite:
  val tests = Tests:
    test("TestRecipe"):
      rvcoverTest {
        val instructionCount = 2
        val r = recipe("TestRecipe", isRVI()) {
          (0 until instructionCount).foreach { i =>
            index(i) {
              isAddi() & 
                rs1Range(1, 32) &
                rdRange(1, 32) &
                imm12Range(0, 100)
            }
          }
          distinct(0 until instructionCount)(_.imm12)
        }
      }
