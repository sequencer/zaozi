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
        val instructionCount = 50
        // rv64gc
        recipe("AddwTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isAddw() & rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
            }
          }

          sequence(0, instructionCount).coverBins(_.rd, (1 until 32).map(i => i.S))
          sequence(0, instructionCount).coverBins(_.rs1, (1 until 32).map(i => i.S))
          sequence(0, instructionCount).coverBins(_.rs2, (1 until 32).map(i => i.S))

          coverSigns(instructionCount, isAddw(), true, true, true)
        }
      }