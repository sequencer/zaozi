// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.decodertest

import me.jiuyang.decoder.{*, given}
import utest.*

object PLASpec extends TestSuite:
  val tests = Tests:
    test("PLA construction"):
      test("should create a valid PLA with basic table"):
        val table   = Seq(
          (BitSet.bitpat("00"), BitSet.bitpat("01")),
          (BitSet.bitpat("01"), BitSet.bitpat("10")),
          (BitSet.bitpat("10"), BitSet.bitpat("11"))
        )
        val default = BitSet.bitpat("00")
        val pla     = PLA(table, default)
        assert(pla.inputWidth == 2)
        assert(pla.outputWidth == 2)
        assert(pla.table.size == 3)
        assert(pla.default == default)
      test("should handle single bit patterns"):
        val table   = Seq(
          (BitSet.bitpat("0"), BitSet.bitpat("1")),
          (BitSet.bitpat("1"), BitSet.bitpat("0"))
        )
        val default = BitSet.bitpat("0")

        val pla = PLA(table, default)

        assert(pla.inputWidth == 1)
        assert(pla.outputWidth == 1)
      test("should work with don't care patterns"):
        val table   = Seq(
          (BitSet.bitpat("1?"), BitSet.bitpat("01")),
          (BitSet.bitpat("0?"), BitSet.bitpat("10"))
        )
        val default = BitSet.bitpat("00")

        val pla = PLA(table, default)

        assert(pla.inputWidth == 2)
        assert(pla.outputWidth == 2)
    test("PLA validation"):
      test("should reject mismatched input widths"):
        val table   = Seq(
          (BitSet.bitpat("00"), BitSet.bitpat("01")), // 2 bits input
          (BitSet.bitpat("1"), BitSet.bitpat("1"))    // 1 bit input - mismatch!
        )
        val default = BitSet.bitpat("00")
        intercept[IllegalArgumentException]:
          PLA(table, default)
      test("should reject mismatched output widths"):
        val table   = Seq(
          (BitSet.bitpat("00"), BitSet.bitpat("01")), // 2 bits output
          (BitSet.bitpat("01"), BitSet.bitpat("1"))   // 1 bit output - mismatch!
        )
        val default = BitSet.bitpat("00")

        intercept[IllegalArgumentException]:
          PLA(table, default)
      test("should reject default with wrong input width"):
        val table   = Seq(
          (BitSet.bitpat("00"), BitSet.bitpat("01"))
        )
        val default = BitSet.bitpat("1") // 1 bit instead of 2
        intercept[IllegalArgumentException]:
          PLA(table, default)
    test("PLA complex patterns"):
      test("should handle complex decoder PLA"):
        val table   = Seq(
          (BitSet.bitpat("0000"), BitSet.bitpat("0001")), // NOP
          (BitSet.bitpat("0001"), BitSet.bitpat("0010")), // ADD
          (BitSet.bitpat("0010"), BitSet.bitpat("0100")), // SUB
          (BitSet.bitpat("0011"), BitSet.bitpat("1000")), // MUL
          (BitSet.bitpat("01??"), BitSet.bitpat("0011")), // LOAD variants
          (BitSet.bitpat("10??"), BitSet.bitpat("0101")), // STORE variants
          (BitSet.bitpat("11??"), BitSet.bitpat("1001"))  // BRANCH variants
        )
        val default = BitSet.bitpat("0000")

        val pla = PLA(table, default)

        assert(pla.inputWidth == 4)
        assert(pla.outputWidth == 4)
        assert(pla.table.size == 7)

        val output = pla.toString

        // Verify specific patterns
        assert(output.contains("01??:0011"))
        assert(output.contains("10??:0101"))
        assert(output.contains("11??:1001"))

      test("should work with wide patterns"):
        val table   = Seq(
          (BitSet.bitpat("00000000"), BitSet.bitpat("11111111")),
          (BitSet.bitpat("11111111"), BitSet.bitpat("00000000")),
          (BitSet.bitpat("????????"), BitSet.bitpat("10101010"))
        )
        val default = BitSet.bitpat("01010101")

        val pla = PLA(table, default)

        assert(pla.inputWidth == 8)
        assert(pla.outputWidth == 8)
        assert(pla.table.size == 3)
    test("PLA integration with TruthTable"):
      test("should work correctly with TruthTable-generated PLAs"):
        import scala.collection.immutable.SortedMap
        val encoding     = SortedMap(
          "ADD"     -> BitSet.bitpat("001"),
          "SUB"     -> BitSet.bitpat("010"),
          "MUL"     -> BitSet.bitpat("100"),
          "default" -> BitSet.bitpat("000")
        )
        val pairs        = Seq(
          (BitSet.bitpat("001"), "ADD"),
          (BitSet.bitpat("010"), "SUB"),
          (BitSet.bitpat("100"), "MUL")
        )
        val truthTable   = TruthTable("alu", pairs, "default", encoding)
        val pla          = PLA(truthTable.table, encoding(truthTable.default))
        assert(pla.inputWidth == 3)
        assert(pla.outputWidth == 3)
        assert(pla.default == BitSet.bitpat("000"))
        // Verify serialization works for TruthTable-generated PLA
        val serialized   = pla.toString
        val deserialized = PLA(serialized)
        assert(deserialized.inputWidth == pla.inputWidth)
        assert(deserialized.outputWidth == pla.outputWidth)
        assert(deserialized.table.size == pla.table.size)
    test("PLA should serialize and deserialize"):
      val pla          = PLA(
        Seq(
          (BitSet.bitpat("00"), BitSet.bitpat("01")),
          (BitSet.bitpat("01"), BitSet.bitpat("10")),
          (BitSet.bitpat("10"), BitSet.bitpat("11"))
        ),
        BitSet.bitpat("00")
      )
      val serialized   = pla.toString
      assert(serialized.contains("00:01"))
      assert(serialized.contains("01:10"))
      assert(serialized.contains("10:11"))
      val deserialized = PLA(serialized)
      assert(pla == deserialized)
