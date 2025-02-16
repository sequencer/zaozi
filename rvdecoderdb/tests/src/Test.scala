// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

package org.chipsalliance.rvdecoderdb.tests

import org.chipsalliance.rvdecoderdb
import utest.*
import os.*

object rvdecoderdbTest extends TestSuite:
  val tests = Tests:
    test("rvdecoderdb works"):
      val riscvOpcodesPath: Path = Path(sys.env.getOrElse("RISCV_OPCODES_INSTALL_PATH", throw new RuntimeException("Environment variable RISCV_OPCODES_INSTALL_PATH not set")))
      val instTable: Iterable[rvdecoderdb.Instruction] = rvdecoderdb.instructions(riscvOpcodesPath)
      instTable.foreach(println)
    