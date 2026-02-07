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
      val totalInstructions = 500
      val perType = totalInstructions / 5

      // Type 1: ADDI (indices 0-99)
      (0 until perType).foreach { i =>
        instruction(i, isAddi()) {
          rdRange(1, 32) & rs1Range(1, 32) & imm12Range(-2048, 2047)
        }
      }

      // Type 2: ADD (indices 100-199)
      (perType until 2 * perType).foreach { i =>
        instruction(i, isAdd()) {
          rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
        }
      }

      // Type 3: SLLI (indices 200-299)
      (2 * perType until 3 * perType).foreach { i =>
        instruction(i, isSlliRV64I()) {
          rdRange(1, 32) & rs1Range(1, 32) & shamtdRange(0, 31)
        }
      }

      // Type 4: XOR (indices 300-399)
      (3 * perType until 4 * perType).foreach { i =>
        instruction(i, isXor()) {
          rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
        }
      }

      // Type 5: MAXU (indices 400-499)
      (4 * perType until 5 * perType).foreach { i =>
        instruction(i, isMaxu()) {
          rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
        }
      }

  test.printInstructions()
  test.writeInstructionsToFile(outputPath)
