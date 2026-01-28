// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvprobe.agent

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.rvprobe.*
import me.jiuyang.rvprobe.constraints.*

import java.nio.file.{Files, Paths}
import scala.util.control.NonFatal

// Run with: mill rvprobe.runMain me.jiuyang.rvprobe.agent.Template out/test.bin
@main def Template(outputPath: String): Unit =
  object test extends RVGenerator:
    val sets          = isRV64GC()
    def constraints() =
      (0 until 20).foreach { i =>
        instruction(i, isSlliRV64I()) {
          rdRange(1, 32) & rs1Range(1, 32)
        }
      }
  
  test.printInstructions()
  test.writeInstructionsToFile(outputPath)
