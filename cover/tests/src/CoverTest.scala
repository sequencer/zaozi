// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

package cover.tests

import rvdecoderdb.*
import utest.*

object RVDecoderDBTest extends TestSuite:
  val tests = Tests:
    test("RVDecoderDB should decode correctly") {
      val decoder = new RVDecoderDB()
      val instruction = 0x00000013 // NOP instruction in RISC-V
      val decoded = decoder.decode(instruction)
      assert(decoded.mnemonic == "NOP")
    }
    