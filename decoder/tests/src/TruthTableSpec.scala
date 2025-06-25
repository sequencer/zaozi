// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.decodertest

import me.jiuyang.decoder.*
import utest.*

import scala.collection.immutable.SortedMap

object TruthTableSpec extends TestSuite:
  val tests = Tests:
    test("TruthTable construction"):
      test("should create a valid truth table with basic encoding"):
        val encoding   = SortedMap(
          "A"       -> BitSet.bitpat("01"),
          "B"       -> BitSet.bitpat("10"),
          "default" -> BitSet.bitpat("00")
        )
        val pairs      = Seq(
          (BitSet.bitpat("00"), "A"),
          (BitSet.bitpat("01"), "B"),
          (BitSet.bitpat("10"), "default")
        )
        val truthTable = TruthTable("test", pairs, "default", encoding)
        assert(truthTable.name == "test")
        assert(truthTable.inputBits == 2)
        assert(truthTable.outputBits == 2)
        assert(truthTable.input.size == 3)
        assert(truthTable.output.size == 3)
        assert(truthTable.table.size == 3)

      test("should handle don't care patterns in encoding"):
        val encoding   = SortedMap(
          "A"       -> BitSet.bitpat("??"),
          "default" -> BitSet.bitpat("00")
        )
        val pairs      = Seq(
          (BitSet.bitpat("11"), "A")
        )
        val truthTable = TruthTable("dontcare", pairs, "default", encoding)
        assert(truthTable.outputBits == 2)
    test("TruthTable validation"):
      test("should reject inconsistent input widths"):
        val encoding = SortedMap("A" -> BitSet.bitpat("1"), "default" -> BitSet.bitpat("0"))
        val pairs    = Seq(
          (BitSet.bitpat("00"), "A"), // 2 bits
          (BitSet.bitpat("1"), "A")   // 1 bit
        )
        intercept[IllegalArgumentException]:
          TruthTable("invalid", pairs, "default", encoding)
      test("should reject unknown encoding references"):
        val encoding = SortedMap("A" -> BitSet.bitpat("1"), "default" -> BitSet.bitpat("0"))
        val pairs    = Seq(
          (BitSet.bitpat("0"), "UNKNOWN")
        )
        intercept[IllegalArgumentException]:
          TruthTable("invalid", pairs, "default", encoding)

      test("should reject inconsistent encoding widths"):
        val encoding = SortedMap(
          "A"       -> BitSet.bitpat("1"),  // 1 bit
          "B"       -> BitSet.bitpat("00"), // 2 bits - inconsistent!
          "default" -> BitSet.bitpat("0")
        )
        val pairs    = Seq(
          (BitSet.bitpat("0"), "A")
        )
        intercept[IllegalArgumentException]:
          TruthTable("invalid", pairs, "default", encoding)

      test("should reject partially defined encodings"):
        val encoding = SortedMap(
          "A"       -> BitSet.bitpat("1?"), // Partially defined - not allowed
          "default" -> BitSet.bitpat("00")
        )
        val pairs    = Seq(
          (BitSet.bitpat("1"), "A")
        )
        intercept[IllegalArgumentException]:
          TruthTable("invalid", pairs, "default", encoding)
      test("should reject overlapping input patterns"):
        val encoding = SortedMap("A" -> BitSet.bitpat("1"), "default" -> BitSet.bitpat("0"))
        val pairs    = Seq(
          (BitSet.bitpat("?0"), "A"), // Overlaps with next
          (BitSet.bitpat("10"), "A")  // Overlaps with previous
        )
        intercept[IllegalArgumentException]:
          TruthTable("invalid", pairs, "default", encoding)
    test("TruthTable properties"):
      val encoding = SortedMap(
        "ADD"     -> BitSet.bitpat("001"),
        "SUB"     -> BitSet.bitpat("010"),
        "MUL"     -> BitSet.bitpat("100"),
        "default" -> BitSet.bitpat("000")
      )

      test("should analyze simple properties"):
        val pairs      = Seq(
          (BitSet.bitpat("0001"), "ADD"),
          (BitSet.bitpat("0010"), "SUB"),
          (BitSet.bitpat("0100"), "MUL"),
          (BitSet.bitpat("1000"), "default")
        )
        val truthTable = TruthTable("alu", pairs, "default", encoding)
        assert(truthTable.inputBits == 4)
        assert(truthTable.outputBits == 3)
        assert(truthTable.input.size == 4)
        assert(truthTable.output.size == 4)
        val inputs     = truthTable.input
        assert(inputs.contains(BitSet.bitpat("0001")))
        assert(inputs.contains(BitSet.bitpat("0010")))
        assert(inputs.contains(BitSet.bitpat("0100")))
        assert(inputs.contains(BitSet.bitpat("1000")))
        val outputs    = truthTable.output
        assert(outputs.contains(BitSet.bitpat("001"))) // ADD
        assert(outputs.contains(BitSet.bitpat("010"))) // SUB
        assert(outputs.contains(BitSet.bitpat("100"))) // MUL
        assert(outputs.contains(BitSet.bitpat("000"))) // default
        val table    = truthTable.table
        assert(table.size == 4)
        val tableMap = table.toMap
        assert(tableMap.contains(BitSet.bitpat("0001")))
        assert(tableMap(BitSet.bitpat("0001")) == BitSet.bitpat("001"))

    test("TruthTable with complex patterns"):
      test("should work with multi-term BitSets"):
        val encoding   = SortedMap(
          "EVEN"    -> BitSet.bitpat("01"),
          "ODD"     -> BitSet.bitpat("10"),
          "default" -> BitSet.bitpat("00")
        )
        val evenBitSet = BitSet(Set(BitSet.bitpat("00"), BitSet.bitpat("10")))
        val oddBitSet  = BitSet(Set(BitSet.bitpat("01"), BitSet.bitpat("11")))
        val pairs      = Seq(
          (evenBitSet, "EVEN"),
          (oddBitSet, "ODD")
        )
        val truthTable = TruthTable("parity_test", pairs, "default", encoding)
        assert(truthTable.inputBits == 2)
        assert(truthTable.outputBits == 2)
        assert(truthTable.table.size == 4) // All 4 possible bit combinations
      test("should work with single bit patterns"):
        val encoding   = SortedMap(
          "HIGH" -> BitSet.bitpat("1"),
          "LOW"  -> BitSet.bitpat("0")
        )
        val pairs      = Seq(
          (BitSet.bitpat("1"), "HIGH"),
          (BitSet.bitpat("0"), "LOW")
        )
        val truthTable = TruthTable("bit_test", pairs, "LOW", encoding)
        assert(truthTable.inputBits == 1)
        assert(truthTable.outputBits == 1)
        assert(truthTable.table.size == 2)
    test("TruthTable to PLA conversion"):
      val encoding   = SortedMap(
        "ADD"     -> BitSet.bitpat("001"),
        "SUB"     -> BitSet.bitpat("010"),
        "default" -> BitSet.bitpat("000")
      )
      val pairs      = Seq(
        (BitSet.bitpat("001"), "ADD"),
        (BitSet.bitpat("010"), "SUB"),
        (BitSet.bitpat("100"), "default")
      )
      val truthTable = TruthTable("simple", pairs, "default", encoding)
      val pla        = PLA(truthTable.table, encoding(truthTable.default))
      test("should have correct dimensions"):
        assert(pla.inputWidth == 3)
        assert(pla.outputWidth == 3)
      test("should have correct table entries"):
        assert(pla.table.size == 3)
        assert(pla.default == BitSet.bitpat("000"))
    test("TruthTable should serialize and deserialize"):
      val encoding     = SortedMap(
        "A"       -> BitSet.bitpat("01"),
        "B"       -> BitSet.bitpat("10"),
        "default" -> BitSet.bitpat("00")
      )
      val pairs        = Seq(
        (BitSet.bitpat("00"), "A"),
        (BitSet.bitpat("01"), "B")
      )
      val original     = TruthTable("serial_test", pairs, "default", encoding)
      val deserialized = TruthTable(original.toString)

      test("should correctly serialize and deserialize"):
        assert(original.toString == "[serial_test][default][A:01,B:10,default:00][00:A,01:B]")
        assert(deserialized == original)

      test("should reject invalid serialized formats"):
        intercept[IllegalArgumentException]:
          TruthTable("invalid_format")
        intercept[IllegalArgumentException]:
          TruthTable("[name][encoding][pairs]") // missing default
        intercept[IllegalArgumentException]:
          TruthTable("[name][A:01][00->A|01->B]") // missing brackets
