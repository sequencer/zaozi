// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.decodertest

import me.jiuyang.decoder.{*, given}
import utest.*

import scala.collection.immutable.SortedMap

object EspressoSpec extends TestSuite:
  val tests = Tests:
    test("Espresso minimization"):
      test("should minimize a simple truth table"):
        val encoding   = SortedMap(
          "HIGH" -> BitSet.bitpat("1"),
          "LOW"  -> BitSet.bitpat("0")
        )
        val pairs      = Seq(
          (BitSet.bitpat("1"), "HIGH"),
          (BitSet.bitpat("0"), "LOW")
        )
        val truthTable = TruthTable("simple", pairs, "LOW", encoding)
        val result     = espresso(Seq(truthTable))
        assert(result.inputWidth == 1)
        assert(result.outputWidth == 1)
        assert(result.default == BitSet.bitpat("0"))

      test("should minimize a more complex truth table"):
        val encoding   = SortedMap(
          "ADD"     -> BitSet.bitpat("001"),
          "SUB"     -> BitSet.bitpat("010"),
          "MUL"     -> BitSet.bitpat("100"),
          "default" -> BitSet.bitpat("000")
        )
        val pairs      = Seq(
          (BitSet.bitpat("0001"), "ADD"),
          (BitSet.bitpat("0010"), "SUB"),
          (BitSet.bitpat("0100"), "MUL")
        )
        val truthTable = TruthTable("alu", pairs, "default", encoding)
        val result     = espresso(Seq(truthTable))
        assert(result.inputWidth == 4)
        assert(result.outputWidth == 3)
        assert(result.default == BitSet.bitpat("000"))
        assert(result.table.nonEmpty)

      test("should handle don't care patterns"):
        val encoding   = SortedMap(
          "MATCH"   -> BitSet.bitpat("1"),
          "NOMATCH" -> BitSet.bitpat("0")
        )
        val pairs      = Seq(
          (BitSet.bitpat("1?"), "MATCH"),
          (BitSet.bitpat("01"), "NOMATCH")
        )
        val truthTable = TruthTable("pattern", pairs, "NOMATCH", encoding)
        val result     = espresso(Seq(truthTable))
        assert(result.inputWidth == 2)
        assert(result.outputWidth == 1)
        assert(result.default == BitSet.bitpat("0"))

      test("should handle multiple truth tables"):
        val encoding1 = SortedMap(
          "A"       -> BitSet.bitpat("1"),
          "default" -> BitSet.bitpat("0")
        )
        val encoding2 = SortedMap(
          "B"       -> BitSet.bitpat("1"),
          "default" -> BitSet.bitpat("0")
        )
        val table1    = TruthTable("t1", Seq((BitSet.bitpat("10"), "A")), "default", encoding1)
        val table2    = TruthTable("t2", Seq((BitSet.bitpat("01"), "B")), "default", encoding2)
        val result    = espresso(Seq(table1, table2))
        assert(result.inputWidth == 2)
        assert(result.outputWidth == 2)
        assert(result.default == BitSet.bitpat("00"))

      test("should handle truth tables with all default values"):
        val encoding   = SortedMap(
          "VAL"     -> BitSet.bitpat("10"),
          "default" -> BitSet.bitpat("00")
        )
        val pairs      = Seq(
          (BitSet.bitpat("00"), "default"),
          (BitSet.bitpat("01"), "default"),
          (BitSet.bitpat("10"), "default"),
          (BitSet.bitpat("11"), "default")
        )
        val truthTable = TruthTable("all_default", pairs, "default", encoding)
        val result     = espresso(Seq(truthTable))
        assert(result.inputWidth == 2)
        assert(result.outputWidth == 2)
        assert(result.default == BitSet.bitpat("00"))
        // Should minimize to empty table since everything maps to default
        assert(result.table.isEmpty || result.table.forall(_._2 == result.default))

      test("should handle single input/output bit"):
        val encoding   = SortedMap(
          "ON"  -> BitSet.bitpat("1"),
          "OFF" -> BitSet.bitpat("0")
        )
        val pairs      = Seq(
          (BitSet.bitpat("1"), "ON")
        )
        val truthTable = TruthTable("single_bit", pairs, "OFF", encoding)
        val result     = espresso(Seq(truthTable))
        assert(result.inputWidth == 1)
        assert(result.outputWidth == 1)
        assert(result.default == BitSet.bitpat("0"))

      test("should preserve output width with mixed defaults"):
        val encoding   = SortedMap(
          "A"       -> BitSet.bitpat("10"),
          "B"       -> BitSet.bitpat("01"),
          "default" -> BitSet.bitpat("??")
        )
        val pairs      = Seq(
          (BitSet.bitpat("00"), "A"),
          (BitSet.bitpat("11"), "B")
        )
        val truthTable = TruthTable("mixed_default", pairs, "default", encoding)
        val result     = espresso(Seq(truthTable))
        assert(result.inputWidth == 2)
        assert(result.outputWidth == 2)
        assert(result.default == BitSet.bitpat("??"))

      test("should handle empty input sequences"):
        intercept[IllegalArgumentException]:
          espresso(Seq.empty)

      test("should minimize redundant entries"):
        val encoding   = SortedMap(
          "HIGH" -> BitSet.bitpat("1"),
          "LOW"  -> BitSet.bitpat("0")
        )
        val pairs      = Seq(
          (BitSet.bitpat("00"), "LOW"),
          (BitSet.bitpat("01"), "HIGH"),
          (BitSet.bitpat("10"), "HIGH"),
          (BitSet.bitpat("11"), "HIGH")
        )
        val truthTable = TruthTable("redundant", pairs, "LOW", encoding)
        val result     = espresso(Seq(truthTable))
        assert(result.inputWidth == 2)
        assert(result.outputWidth == 1)
        assert(result.default == BitSet.bitpat("0"))
        assert(result.table.size <= pairs.size)

      test("should handle multi-bit outputs correctly"):
        val encoding   = SortedMap(
          "CMD1" -> BitSet.bitpat("001"),
          "CMD2" -> BitSet.bitpat("010"),
          "CMD3" -> BitSet.bitpat("100"),
          "IDLE" -> BitSet.bitpat("000")
        )
        val pairs      = Seq(
          (BitSet.bitpat("01"), "CMD1"),
          (BitSet.bitpat("10"), "CMD2"),
          (BitSet.bitpat("11"), "CMD3")
        )
        val truthTable = TruthTable("multi_bit", pairs, "IDLE", encoding)
        val result     = espresso(Seq(truthTable))
        assert(result.inputWidth == 2)
        assert(result.outputWidth == 3)
        assert(result.default == BitSet.bitpat("000"))
        // Verify the mapping is preserved
        val resultMap  = result.table.toMap
        assert(resultMap.size >= 3) // At least our three mappings

      test("should handle complex multi-term BitSets"):
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
        val truthTable = TruthTable("parity", pairs, "default", encoding)
        val result     = espresso(Seq(truthTable))
        assert(result.inputWidth == 2)
        assert(result.outputWidth == 2)
        assert(result.default == BitSet.bitpat("00"))
        // Should have all 4 input combinations mapped
        assert(result.toString.contains("?0:01"))

      test("should work with different default types"):
        // Test with all-ones default
        val encoding1 = SortedMap(
          "ZERO"    -> BitSet.bitpat("00"),
          "default" -> BitSet.bitpat("11")
        )
        val table1    = TruthTable("ones_default", Seq((BitSet.bitpat("00"), "ZERO")), "default", encoding1)
        val result1   = espresso(Seq(table1))
        assert(result1.inputWidth == 2)
        assert(result1.outputWidth == 2)
        assert(result1.default == BitSet.bitpat("11"))
        // Test with all-zeros default
        val encoding2 = SortedMap(
          "ONE"     -> BitSet.bitpat("11"),
          "default" -> BitSet.bitpat("00")
        )
        val table2    = TruthTable("zeros_default", Seq((BitSet.bitpat("11"), "ONE")), "default", encoding2)
        val result2   = espresso(Seq(table2))
        assert(result2.inputWidth == 2)
        assert(result2.outputWidth == 2)
        assert(result2.default == BitSet.bitpat("00"))

      test("result should be functionally equivalent to input"):
        val encoding   = SortedMap(
          "A"       -> BitSet.bitpat("01"),
          "B"       -> BitSet.bitpat("10"),
          "C"       -> BitSet.bitpat("11"),
          "default" -> BitSet.bitpat("00")
        )
        val pairs      = Seq(
          (BitSet.bitpat("001"), "A"),
          (BitSet.bitpat("010"), "B"),
          (BitSet.bitpat("100"), "C")
        )
        val truthTable = TruthTable("equivalence_test", pairs, "default", encoding)
        val result     = espresso(Seq(truthTable))
        // Create a lookup function for the result
        def lookup(input: BitPat): BitPat =
          result.table.find(_._1 == input).map(_._2).getOrElse(result.default)
        // Test all original mappings are preserved
        assert(lookup(BitSet.bitpat("001")) == BitSet.bitpat("01"))
        assert(lookup(BitSet.bitpat("010")) == BitSet.bitpat("10"))
        assert(lookup(BitSet.bitpat("100")) == BitSet.bitpat("11"))
        // Test unmapped inputs return default
        assert(lookup(BitSet.bitpat("000")) == BitSet.bitpat("00"))
        assert(lookup(BitSet.bitpat("111")) == BitSet.bitpat("00"))

      // TODO: I think bug here... wait for formal
      test("should handle mixed default types that require splitting"):
        // DC
        val encoding1 = SortedMap(
          "ON"      -> BitSet.bitpat("1"),
          "OFF"     -> BitSet.bitpat("0"),
          "default" -> BitSet.bitpat("?")
        )
        val pair1     = Seq(
          (BitSet.bitpat("01"), "ON"),
          (BitSet.bitpat("10"), "OFF")
        )
        val table1    = TruthTable("table1", pair1, "default", encoding1)
        val result1   = espresso(Seq(table1))
        // (?1,1)

        // default -> 0/1
        val encoding2 = SortedMap(
          "ADD" -> BitSet.bitpat("01"),
          "MUL" -> BitSet.bitpat("10"),
          "DIV" -> BitSet.bitpat("11")
        )
        val pair2     = Seq(
          (BitSet.bitpat("01"), "ADD"),
          (BitSet.bitpat("10"), "MUL"),
          (BitSet.bitpat("11"), "DIV")
        )
        val table2    = TruthTable("alu", pair2, "ADD", encoding2)
        val result2   = espresso(Seq(table2))
        // (10,?1), (1?,1?)

        // Test combined tables with mixed defaults
        val result3 = espresso(Seq(table1, table2))
        // (10,??1), (1?,?1?), (?1,1??)

      test("should handle complex mixed default with zeros, ones and don't cares"):
        // Test default with mix of 0, 1, and ? (10?1?0)
        val encoding = SortedMap(
          "A"       -> BitSet.bitpat("000000"),
          "B"       -> BitSet.bitpat("111111"),
          "default" -> BitSet.bitpat("10?1?0")
        )
        val pairs    = Seq(
          (BitSet.bitpat("001"), "A"),
          (BitSet.bitpat("110"), "B")
        )
        intercept[IllegalArgumentException]:
          TruthTable("complex_mixed_default", pairs, "default", encoding)
