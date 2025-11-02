// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvprobe.apps

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.rvprobe.*
import me.jiuyang.rvprobe.constraints.*

// Run with: mill rvprobe.runMain me.jiuyang.rvprobe.apps.RV32I
object RV32I extends App:
  val instructionCount = 40

  object Slli extends RVGenerator:
    val sets          = isRV64GC()
    def constraints() =
      (0 until instructionCount).foreach { i =>
        instruction(i) {
          isSlliRV64I() & rdRange(1, 32) & rs1Range(1, 32)
        }
      }

      coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
      coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))

      coverRAWHazards(0 until instructionCount, true, true)
      coverWARHazards(0 until instructionCount, true, true)
      coverWAWHazards(0 until instructionCount, true, true)
      coverNoHazards(0 until instructionCount, true, true)

      coverSigns(instructionCount, isSlliRV64I(), true, true)

  Slli.writeInstructionsToFile("out/rv32i.bin")
