// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

package cover.tests

import org.chipsalliance.rvdecoderdb
import utest.*
import os.*

object RVDecoderDBTest extends TestSuite:
  val tests = Tests:
    test("rvdecoderdb works") {
      val instTable: Iterable[rvdecoderdb.Instruction] = rvdecoderdb.instructions(os.pwd / "rvdecoderdb" / "rvdecoderdbtest" / "jvm" / "riscv-opcodes")
      instTable.foreach { case inst: rvdecoderdb.Instruction =>
        println(inst.toString)
      }
    }
    