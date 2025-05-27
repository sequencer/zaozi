// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvcover.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.tpe.*
import me.jiuyang.rvcover.*

import os.Path
import java.io.{File, FileWriter}

import utest.*

object RecipeTest extends TestSuite:
  val tests = Tests:
    test("TestRecipe"):
      rvcoverTest {
        val r = recipe("TestRecipe", isRVI()) {
          index(0) {
            isAddi()
              & rdRange(1, 2)
              & rs1Range(1, 32)
              & imm20Range(0, 1024)
          }
        }

        assert(r.name == "TestRecipe")
        println(r)

        val writer = new FileWriter(new File("./output.template"), true)
        writer.write(r.toString())
        writer.close()
      }
