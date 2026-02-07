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
      (0 until 100).foreach { i =>
        val opcode: Index ?=> InstConstraint = i % 3 match {
          case 0 => isAddi()
          case 1 => isAdd()
          case 2 => isAddw()
        }
        instruction(i, opcode) {
          rdRange(1, 32) & rs1Range(1, 32) & (if (i % 3 == 0) imm12Range(-100, 100) else rs2Range(1, 32))
        }
      }

  test.printInstructions()
  test.writeInstructionsToFile(outputPath)
