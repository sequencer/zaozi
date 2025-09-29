// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvprobe.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.tpe.*
import me.jiuyang.rvprobe.*

import utest.*

object RV32I extends TestSuite:
  val tests = Tests:
    test("Slli"):
      rvprobeTest {
        val instructionCount = 50
        recipe("SlliTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
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
        }
      }
    test("Srai"):
      rvprobeTest {
        val instructionCount = 50
        recipe("SraiTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isSraiRV64I() & rdRange(1, 32) & rs1Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))

          coverRAWHazards(0 until instructionCount, true, true)
          coverWARHazards(0 until instructionCount, true, true)
          coverWAWHazards(0 until instructionCount, true, true)
          coverNoHazards(0 until instructionCount, true, true)

          coverSigns(instructionCount, isSraiRV64I(), true, true)
        }
      }
    test("Srli"):
      rvprobeTest {
        val instructionCount = 50
        recipe("SrliTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isSrliRV64I() & rdRange(1, 32) & rs1Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))

          coverRAWHazards(0 until instructionCount, true, true)
          coverWARHazards(0 until instructionCount, true, true)
          coverWAWHazards(0 until instructionCount, true, true)
          coverNoHazards(0 until instructionCount, true, true)

          coverSigns(instructionCount, isSrliRV64I(), true, true)
        }
      }
    test("Slli"):
      rvprobeTest {
        val instructionCount = 50
        recipe("SlliTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
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
        }
      }
    test("Srai"):
      rvprobeTest {
        val instructionCount = 50
        recipe("SraiTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isSraiRV64I() & rdRange(1, 32) & rs1Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))

          coverRAWHazards(0 until instructionCount, true, true)
          coverWARHazards(0 until instructionCount, true, true)
          coverWAWHazards(0 until instructionCount, true, true)
          coverNoHazards(0 until instructionCount, true, true)

          coverSigns(instructionCount, isSraiRV64I(), true, true)
        }
      }
    test("Srli"):
      rvprobeTest {
        val instructionCount = 50
        recipe("SrliTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isSrliRV64I() & rdRange(1, 32) & rs1Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))

          coverRAWHazards(0 until instructionCount, true, true)
          coverWARHazards(0 until instructionCount, true, true)
          coverWAWHazards(0 until instructionCount, true, true)
          coverNoHazards(0 until instructionCount, true, true)

          coverSigns(instructionCount, isSrliRV64I(), true, true)
        }
      }
    test("Add"):
      rvprobeTest {
        val instructionCount = 50
        recipe("AddTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isAdd() & rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs2, (1 until 32).map(i => i.S))

          coverRAWHazards(0 until instructionCount, true, true, true)
          coverWARHazards(0 until instructionCount, true, true, true)
          coverWAWHazards(0 until instructionCount, true, true, true)
          coverNoHazards(0 until instructionCount, true, true, true)

          coverSigns(instructionCount, isAdd(), true, true, true)
        }
      }
    test("Addi"):
      rvprobeTest {
        val instructionCount = 50
        recipe("AddiTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isAddi() & rdRange(1, 32) & rs1Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.imm12, Seq((-1).S, 0.S, 1.S, (-2048).S, 2047.S))

          coverRAWHazards(0 until instructionCount, true, true)
          coverWARHazards(0 until instructionCount, true, true)
          coverWAWHazards(0 until instructionCount, true, true)
          coverNoHazards(0 until instructionCount, true, true)

          coverSigns(instructionCount, isAddi(), true, true)
        }
      }
    test("And"):
      rvprobeTest {
        val instructionCount = 50
        recipe("AndTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isAnd() & rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs2, (1 until 32).map(i => i.S))

          coverRAWHazards(0 until instructionCount, true, true, true)
          coverWARHazards(0 until instructionCount, true, true, true)
          coverWAWHazards(0 until instructionCount, true, true, true)
          coverNoHazards(0 until instructionCount, true, true, true)

          coverSigns(instructionCount, isAnd(), true, true, true)
        }
      }
    test("Andi"):
      rvprobeTest {
        val instructionCount = 50
        recipe("AndiTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isAndi() & rdRange(1, 32) & rs1Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.imm12, Seq((-1).S, 0.S, 1.S, (-2048).S, 2047.S))

          coverRAWHazards(0 until instructionCount, true, true)
          coverWARHazards(0 until instructionCount, true, true)
          coverWAWHazards(0 until instructionCount, true, true)
          coverNoHazards(0 until instructionCount, true, true)

          coverSigns(instructionCount, isAndi(), true, true)
        }
      }
    test("Auipc"):
      rvprobeTest {
        val instructionCount = 50
        recipe("AuipcTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isAuipc() & rdRange(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.imm20, Seq((-1).S, 0.S, 1.S, (-524288).S, 524287.S))

          coverRAWHazards(0 until instructionCount, true)
          coverWARHazards(0 until instructionCount, true)
          coverWAWHazards(0 until instructionCount, true)
          coverNoHazards(0 until instructionCount, true)

          coverSigns(instructionCount, isAuipc(), true)
        }
      }
      test("Beq"):
        rvprobeTest {
          val instructionCount = 40
          recipe("BeqTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
            (0 until 5).foreach { i =>
              instruction(i) {
                isAddi() & rdRange(i+1, i+2) & rs1Range(0, 1) & imm12Range(-5, -1)
              }
            }

            (5 until instructionCount+5).foreach { i =>
              instruction(i) {
                isBeq() & rs1Range(1, 32) & rs2Range(1, 32) & bimm12loRange(4, 5) & bimm12hiRange(0, 1)
              }
            }

            coverBins(5 until instructionCount+5)(_.rs1, (1 until 32).map(i => i.S))
            coverBins(5 until instructionCount+5)(_.rs2, (1 until 32).map(i => i.S))

            coverSigns(instructionCount+5, isBeq() & bimm12loRange(4, 5) & bimm12hiRange(0, 1), true, true)
          }
        }
      test("Bge"):
        rvprobeTest {
          val instructionCount = 40
          recipe("BgeTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
            (0 until 5).foreach { i =>
              instruction(i) {
                isAddi() & rdRange(i+1, i+2) & rs1Range(0, 1) & imm12Range(-5, -1)
              }
            }

            (5 until instructionCount+5).foreach { i =>
              instruction(i) {
                isBge() & rs1Range(1, 32) & rs2Range(1, 32) & bimm12loRange(4, 5) & bimm12hiRange(0, 1)
              }
            }

            coverBins(5 until instructionCount+5)(_.rs1, (1 until 32).map(i => i.S))
            coverBins(5 until instructionCount+5)(_.rs2, (1 until 32).map(i => i.S))

            coverSigns(instructionCount+5, isBge() & bimm12loRange(4, 5) & bimm12hiRange(0, 1), true, true)
          }
        }
      test("Bgeu"):
        rvprobeTest {
          val instructionCount = 40
          recipe("BgeuTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
            (0 until 5).foreach { i =>
              instruction(i) {
                isAddi() & rdRange(i+1, i+2) & rs1Range(0, 1) & imm12Range(-5, -1)
              }
            }

            (5 until instructionCount+5).foreach { i =>
              instruction(i) {
                isBgeu() & rs1Range(1, 32) & rs2Range(1, 32) & bimm12loRange(4, 5) & bimm12hiRange(0, 1)
              }
            }

            coverBins(5 until instructionCount+5)(_.rs1, (1 until 32).map(i => i.S))
            coverBins(5 until instructionCount+5)(_.rs2, (1 until 32).map(i => i.S))

            coverSigns(instructionCount+5, isBgeu() & bimm12loRange(4, 5) & bimm12hiRange(0, 1), true, true)
          }
        }
      test("Blt"):
        rvprobeTest {
          val instructionCount = 40
          recipe("BltTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
            (0 until 5).foreach { i =>
              instruction(i) {
                isAddi() & rdRange(i+1, i+2) & rs1Range(0, 1) & imm12Range(-5, -1)
              }
            }

            (5 until instructionCount+5).foreach { i =>
              instruction(i) {
                isBlt() & rs1Range(1, 32) & rs2Range(1, 32) & bimm12loRange(4, 5) & bimm12hiRange(0, 1)
              }
            }

            coverBins(5 until instructionCount+5)(_.rs1, (1 until 32).map(i => i.S))
            coverBins(5 until instructionCount+5)(_.rs2, (1 until 32).map(i => i.S))

            coverSigns(instructionCount+5, isBlt() & bimm12loRange(4, 5) & bimm12hiRange(0, 1), true, true)
          }
        }
      test("Bltu"):
        rvprobeTest {
          val instructionCount = 40
          recipe("BltuTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
            (0 until 5).foreach { i =>
              instruction(i) {
                isAddi() & rdRange(i+1, i+2) & rs1Range(0, 1) & imm12Range(-5, -1)
              }
            }

            (5 until instructionCount+5).foreach { i =>
              instruction(i) {
                isBltu() & rs1Range(1, 32) & rs2Range(1, 32) & bimm12loRange(4, 5) & bimm12hiRange(0, 1)
              }
            }

            coverBins(5 until instructionCount+5)(_.rs1, (1 until 32).map(i => i.S))
            coverBins(5 until instructionCount+5)(_.rs2, (1 until 32).map(i => i.S))

            coverSigns(instructionCount+5, isBltu() & bimm12loRange(4, 5) & bimm12hiRange(0, 1), true, true)
          }
        }
      test("Bne"):
        rvprobeTest {
          val instructionCount = 40
          recipe("BneTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
            (0 until 5).foreach { i =>
              instruction(i) {
                isAddi() & rdRange(i+1, i+2) & rs1Range(0, 1) & imm12Range(-5, -1)
              }
            }

            (5 until instructionCount+5).foreach { i =>
              instruction(i) {
                isBne() & rs1Range(1, 32) & rs2Range(1, 32) & bimm12loRange(4, 5) & bimm12hiRange(0, 1)
              }
            }

            coverBins(5 until instructionCount+5)(_.rs1, (1 until 32).map(i => i.S))
            coverBins(5 until instructionCount+5)(_.rs2, (1 until 32).map(i => i.S))

            coverSigns(instructionCount+5, isBne() & bimm12loRange(4, 5) & bimm12hiRange(0, 1), true, true)
          }
        }
    test("Lui"):
      rvprobeTest {
        val instructionCount = 50
        recipe("LuiTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isLui() & rdRange(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.imm20, Seq((-1).S, 0.S, 1.S, (-524288).S, 524287.S))

          coverRAWHazards(0 until instructionCount, true)
          coverWARHazards(0 until instructionCount, true)
          coverWAWHazards(0 until instructionCount, true)
          coverNoHazards(0 until instructionCount, true)

          coverSigns(instructionCount, isLui(), true)
        }
      }
    test("Or"):
      rvprobeTest {
        val instructionCount = 50
        recipe("OrTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isOr() & rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs2, (1 until 32).map(i => i.S))

          coverRAWHazards(0 until instructionCount, true, true, true)
          coverWARHazards(0 until instructionCount, true, true, true)
          coverWAWHazards(0 until instructionCount, true, true, true)
          coverNoHazards(0 until instructionCount, true, true, true)

          coverSigns(instructionCount, isOr(), true, true, true)
        }
      }
    test("Ori"):
      rvprobeTest {
        val instructionCount = 50
        recipe("OriTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isOri() & rdRange(1, 32) & rs1Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.imm12, Seq((-1).S, 0.S, 1.S, (-2048).S, 2047.S))

          coverRAWHazards(0 until instructionCount, true, true)
          coverWARHazards(0 until instructionCount, true, true)
          coverWAWHazards(0 until instructionCount, true, true)
          coverNoHazards(0 until instructionCount, true, true)

          coverSigns(instructionCount, isOri(), true, true)
        }
      }
    test("Sll"):
      rvprobeTest {
        val instructionCount = 50
        recipe("SllTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isSll() & rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs2, (1 until 32).map(i => i.S))

          coverRAWHazards(0 until instructionCount, true, true, true)
          coverWARHazards(0 until instructionCount, true, true, true)
          coverWAWHazards(0 until instructionCount, true, true, true)
          coverNoHazards(0 until instructionCount, true, true, true)

          coverSigns(instructionCount, isSll(), true, true, true)
        }
      }
    test("Slt"):
      rvprobeTest {
        val instructionCount = 50
        recipe("SltTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isSlt() & rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs2, (1 until 32).map(i => i.S))

          coverRAWHazards(0 until instructionCount, true, true, true)
          coverWARHazards(0 until instructionCount, true, true, true)
          coverWAWHazards(0 until instructionCount, true, true, true)
          coverNoHazards(0 until instructionCount, true, true, true)

          coverSigns(instructionCount, isSlt(), true, true, true)
        }
      }
    test("Slti"):
      rvprobeTest {
        val instructionCount = 50
        recipe("SltiTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isSlti() & rdRange(1, 32) & rs1Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.imm12, Seq((-1).S, 0.S, 1.S, (-2048).S, 2047.S))

          coverRAWHazards(0 until instructionCount, true, true)
          coverWARHazards(0 until instructionCount, true, true)
          coverWAWHazards(0 until instructionCount, true, true)
          coverNoHazards(0 until instructionCount, true, true)

          coverSigns(instructionCount, isSlti(), true, true)
        }
      }
    test("Sltiu"):
      rvprobeTest {
        val instructionCount = 50
        recipe("SltiuTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isSltiu() & rdRange(1, 32) & rs1Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.imm12, Seq((-1).S, 0.S, 1.S, (-2048).S, 2047.S))

          coverRAWHazards(0 until instructionCount, true, true)
          coverWARHazards(0 until instructionCount, true, true)
          coverWAWHazards(0 until instructionCount, true, true)
          coverNoHazards(0 until instructionCount, true, true)

          coverSigns(instructionCount, isSltiu(), true, true)
        }
      }
    test("Sltu"):
      rvprobeTest {
        val instructionCount = 50
        recipe("SltuTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isSltu() & rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs2, (1 until 32).map(i => i.S))

          coverRAWHazards(0 until instructionCount, true, true, true)
          coverWARHazards(0 until instructionCount, true, true, true)
          coverWAWHazards(0 until instructionCount, true, true, true)
          coverNoHazards(0 until instructionCount, true, true, true)

          coverSigns(instructionCount, isSltu(), true, true, true)
        }
      }
    test("Sra"):
      rvprobeTest {
        val instructionCount = 50
        recipe("SraTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isSra() & rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs2, (1 until 32).map(i => i.S))

          coverRAWHazards(0 until instructionCount, true, true, true)
          coverWARHazards(0 until instructionCount, true, true, true)
          coverWAWHazards(0 until instructionCount, true, true, true)
          coverNoHazards(0 until instructionCount, true, true, true)

          coverSigns(instructionCount, isSra(), true, true, true)
        }
      }
    test("Srl"):
      rvprobeTest {
        val instructionCount = 50
        recipe("SrlTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isSrl() & rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs2, (1 until 32).map(i => i.S))

          coverRAWHazards(0 until instructionCount, true, true, true)
          coverWARHazards(0 until instructionCount, true, true, true)
          coverWAWHazards(0 until instructionCount, true, true, true)
          coverNoHazards(0 until instructionCount, true, true, true)

          coverSigns(instructionCount, isSrl(), true, true, true)
        }
      }
    test("Sub"):
      rvprobeTest {
        val instructionCount = 50
        recipe("SubTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isSub() & rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs2, (1 until 32).map(i => i.S))

          coverRAWHazards(0 until instructionCount, true, true, true)
          coverWARHazards(0 until instructionCount, true, true, true)
          coverWAWHazards(0 until instructionCount, true, true, true)
          coverNoHazards(0 until instructionCount, true, true, true)

          coverSigns(instructionCount, isSub(), true, true, true)
        }
      }
    test("Xor"):
      rvprobeTest {
        val instructionCount = 50
        recipe("XorTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isXor() & rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs2, (1 until 32).map(i => i.S))

          coverRAWHazards(0 until instructionCount, true, true, true)
          coverWARHazards(0 until instructionCount, true, true, true)
          coverWAWHazards(0 until instructionCount, true, true, true)
          coverNoHazards(0 until instructionCount, true, true, true)

          coverSigns(instructionCount, isXor(), true, true, true)
        }
      }
    test("Xori"):
      rvprobeTest {
        val instructionCount = 50
        recipe("XoriTests", isRVI(), isRVM(), isRVA(), isRVF(), isRVD(), isRV64I(), isRV64M(), isRV64A(), isRV64F(), isRV64D(), isRV64C()) {
          (0 until instructionCount).foreach { i =>
            instruction(i) {
              isXori() & rdRange(1, 32) & rs1Range(1, 32)
            }
          }

          coverBins(0 until instructionCount)(_.rd, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.rs1, (1 until 32).map(i => i.S))
          coverBins(0 until instructionCount)(_.imm12, Seq((-1).S, 0.S, 1.S, (-2048).S, 2047.S))

          coverRAWHazards(0 until instructionCount, true, true)
          coverWARHazards(0 until instructionCount, true, true)
          coverWAWHazards(0 until instructionCount, true, true)
          coverNoHazards(0 until instructionCount, true, true)

          coverSigns(instructionCount, isXori(), true, true)
        }
      }