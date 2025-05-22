// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvcover.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.tpe.*
import me.jiuyang.rvcover.*

import org.chipsalliance.rvdecoderdb.*
import os.Path

import utest.*

import java.lang.foreign.Arena

object InstructionTest extends TestSuite:
  val tests = Tests:
    test("import rvdecoderdb success"):
      val riscvOpcodesPath: Path = Path(
        sys.env.getOrElse(
          "RISCV_OPCODES_INSTALL_PATH",
          throw new RuntimeException("Environment variable RISCV_OPCODES_INSTALL_PATH not set")
        )
      )
      val instTable: Iterable[Instruction] = instructions(riscvOpcodesPath)
      // instTable.foreach(println)
      assert(instTable.nonEmpty)
