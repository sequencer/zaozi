// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvprobe.agent

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.rvprobe.*
import me.jiuyang.rvprobe.constraints.*

import java.nio.file.{Files, Paths}
import scala.util.control.NonFatal

// Run with: nix develop . -c mill rvprobe.runMain me.jiuyang.rvprobe.agent.Test out/test.bin
@main def Test(outputPath: String): Unit =
  object test extends RVGenerator:
    val sets          = isRV64GC()
    def constraints() =
      (0 until 50).foreach { i =>
        val regDst = (i % 30) + 1   // rd cycles through 1-30
        val regSrc = if (i == 0) 1 else ((i - 1) % 30) + 1  // rs1 = previous rd
        if (i % 2 == 0) {
          instruction(i, isAddi()) {
            rdRange(regDst, regDst + 1) & rs1Range(regSrc, regSrc + 1) & imm12Range(-10, 10)
          }
        } else {
          instruction(i, isSub()) {
            rdRange(regDst, regDst + 1) & rs1Range(regSrc, regSrc + 1) & rs2Range(1, 32)
          }
        }
      }

  test.printInstructions()
  test.writeInstructionsToFile(outputPath)
