// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvcover.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.tpe.*
import me.jiuyang.rvcover.*

import utest.*

import org.chipsalliance.rvdecoderdb.*

import java.io.{File, FileWriter}

import java.lang.foreign.Arena

object RecipeTest extends TestSuite:
  val tests = Tests:
    test("TestRecipe"):
      rvcoverTest {
        val recipe = Recipe("TestRecipe")

        val rs1 = Rs1()

        rs1.addConstraint(rs1.value > 4.S)

        val add = Inst("add", List(Rd(), rs1, Rs2()))

        recipe.addInstruction(add)

        println(recipe.toString())

        // output file
        val writer = new FileWriter(new File("./output.smt2"), false)
        writer.write(recipe.toString + "\n" + "====================\n")
        writer.close()

        recipe.cook()
      }
