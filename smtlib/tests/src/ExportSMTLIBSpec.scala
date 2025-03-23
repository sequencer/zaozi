// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.smtlib.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.tpe.*
import me.jiuyang.smtlib.*
import utest.*

import java.lang.foreign.Arena

object ExportSMTLIBSpec extends TestSuite:
  val tests = Tests:
    test("Check"):
      smtTest(
        "; solver scope 0",
        "(check-sat)",
        "(reset)"
      ):
        // mlir format
        // "func.func"() ({
        //   "smt.solver"() ({
        //     "smt.check"() ({
        //     }, {
        //     }, {
        //     }) : () -> ()
        //   }) : () -> ()
        // }) {symName = "func"} : () -> ()

        // smt-lib2 format
        // ; solver scope 0
        // (check-sat)
        // (reset)
        solver { smtCheck }
    test("Sudoku"):
      smtTest(
        "(set-logic QF_LIA)",
        "(declare-const f1 Int)",
        "(declare-const f2 Int)",
        "(declare-const f3 Int)",
        "(declare-const f4 Int)",
        "(declare-const f5 Int)",
        "(declare-const f6 Int)",
        "(declare-const f7 Int)",
        "(declare-const f8 Int)",
        "(declare-const f9 Int)",
        "(declare-const s Int)",
        "(assert (let ((tmp (distinct f1 f2 f3 f4 f5 f6 f7 f8 f9)))",
        "        (let ((tmp_0 (<= f9 9)))",
        "        (let ((tmp_1 (>= f9 1)))",
        "        (let ((tmp_2 (<= f8 9)))",
        "        (let ((tmp_3 (>= f8 1)))",
        "        (let ((tmp_4 (<= f7 9)))",
        "        (let ((tmp_5 (>= f7 1)))",
        "        (let ((tmp_6 (<= f6 9)))",
        "        (let ((tmp_7 (>= f6 1)))",
        "        (let ((tmp_8 (<= f5 9)))",
        "        (let ((tmp_9 (>= f5 1)))",
        "        (let ((tmp_10 (<= f4 9)))",
        "        (let ((tmp_11 (>= f4 1)))",
        "        (let ((tmp_12 (<= f3 9)))",
        "        (let ((tmp_13 (>= f3 1)))",
        "        (let ((tmp_14 (<= f2 9)))",
        "        (let ((tmp_15 (>= f2 1)))",
        "        (let ((tmp_16 (<= f1 9)))",
        "        (let ((tmp_17 (>= f1 1)))",
        "        (let ((tmp_18 (and tmp_17 tmp_16)))",
        "        (let ((tmp_19 (and tmp_18 tmp_15)))",
        "        (let ((tmp_20 (and tmp_19 tmp_14)))",
        "        (let ((tmp_21 (and tmp_20 tmp_13)))",
        "        (let ((tmp_22 (and tmp_21 tmp_12)))",
        "        (let ((tmp_23 (and tmp_22 tmp_11)))",
        "        (let ((tmp_24 (and tmp_23 tmp_10)))",
        "        (let ((tmp_25 (and tmp_24 tmp_9)))",
        "        (let ((tmp_26 (and tmp_25 tmp_8)))",
        "        (let ((tmp_27 (and tmp_26 tmp_7)))",
        "        (let ((tmp_28 (and tmp_27 tmp_6)))",
        "        (let ((tmp_29 (and tmp_28 tmp_5)))",
        "        (let ((tmp_30 (and tmp_29 tmp_4)))",
        "        (let ((tmp_31 (and tmp_30 tmp_3)))",
        "        (let ((tmp_32 (and tmp_31 tmp_2)))",
        "        (let ((tmp_33 (and tmp_32 tmp_1)))",
        "        (let ((tmp_34 (and tmp_33 tmp_0)))",
        "        (let ((tmp_35 (and tmp_34 tmp)))",
        "        tmp_35))))))))))))))))))))))))))))))))))))))",
        "(assert (let ((tmp_36 (+ f1 f2)))",
        "        (let ((tmp_37 (+ tmp_36 f3)))",
        "        (let ((tmp_38 (= s tmp_37)))",
        "        tmp_38))))",
        "(assert (let ((tmp_39 (+ f4 f5)))",
        "        (let ((tmp_40 (+ tmp_39 f6)))",
        "        (let ((tmp_41 (= s tmp_40)))",
        "        tmp_41))))",
        "(assert (let ((tmp_42 (+ f7 f8)))",
        "        (let ((tmp_43 (+ tmp_42 f9)))",
        "        (let ((tmp_44 (= s tmp_43)))",
        "        tmp_44))))",
        "(assert (let ((tmp_45 (+ f1 f4)))",
        "        (let ((tmp_46 (+ tmp_45 f7)))",
        "        (let ((tmp_47 (= s tmp_46)))",
        "        tmp_47))))",
        "(assert (let ((tmp_48 (+ f2 f5)))",
        "        (let ((tmp_49 (+ tmp_48 f8)))",
        "        (let ((tmp_50 (= s tmp_49)))",
        "        tmp_50))))",
        "(assert (let ((tmp_51 (+ f3 f6)))",
        "        (let ((tmp_52 (+ tmp_51 f9)))",
        "        (let ((tmp_53 (= s tmp_52)))",
        "        tmp_53))))",
        "(assert (let ((tmp_54 (+ f1 f5)))",
        "        (let ((tmp_55 (+ tmp_54 f9)))",
        "        (let ((tmp_56 (= s tmp_55)))",
        "        tmp_56))))",
        "(assert (let ((tmp_57 (+ f3 f5)))",
        "        (let ((tmp_58 (+ tmp_57 f7)))",
        "        (let ((tmp_59 (= s tmp_58)))",
        "        tmp_59))))",
        "(check-sat)",
        "(reset)"
      ):
        // smt-lib2 format
        solver {
          // (set-logic QF_LIA)
          smtSetLogic("QF_LIA")

          // (declare-fun f1 () Int)
          // (declare-fun f2 () Int)
          // (declare-fun f3 () Int)
          // (declare-fun f4 () Int)
          // (declare-fun f5 () Int)
          // (declare-fun f6 () Int)
          // (declare-fun f7 () Int)
          // (declare-fun f8 () Int)
          // (declare-fun f9 () Int)
          // (declare-fun s () Int)

          val f1 = smtValue(SInt)
          val f2 = smtValue(SInt)
          val f3 = smtValue(SInt)
          val f4 = smtValue(SInt)
          val f5 = smtValue(SInt)
          val f6 = smtValue(SInt)
          val f7 = smtValue(SInt)
          val f8 = smtValue(SInt)
          val f9 = smtValue(SInt)
          val s  = smtValue(SInt)

          // (assert (and (>= f1 1) (<= f1 9)))
          // (assert (and (>= f2 1) (<= f2 9)))
          // (assert (and (>= f3 1) (<= f3 9)))
          // (assert (and (>= f4 1) (<= f4 9)))
          // (assert (and (>= f5 1) (<= f5 9)))
          // (assert (and (>= f6 1) (<= f6 9)))
          // (assert (and (>= f7 1) (<= f7 9)))
          // (assert (and (>= f8 1) (<= f8 9)))
          // (assert (and (>= f9 1) (<= f9 9)))
          // (assert (distinct f1 f2 f3 f4 f5 f6 f7 f8 f9))

          smtAssert(
            f1 >= 1.S & f1 <= 9.S & f2 >= 1.S & f2 <= 9.S & f3 >= 1.S & f3 <= 9.S & f4 >= 1.S & f4 <= 9.S &
              f5 >= 1.S & f5 <= 9.S & f6 >= 1.S & f6 <= 9.S & f7 >= 1.S & f7 <= 9.S & f8 >= 1.S & f8 <= 9.S &
              f9 >= 1.S & f9 <= 9.S & smtDistinct(f1, f2, f3, f4, f5, f6, f7, f8, f9)
          )

          // (assert (= s ( f1 f2 f3)))
          // (assert (= s (+ f4 f5 f6)))
          // (assert (= s (+ f7 f8 f9)))
          // (assert (= s (+ f1 f4 f7)))
          // (assert (= s (+ f2 f5 f8)))
          // (assert (= s (+ f3 f6 f9)))
          // (assert (= s (+ f1 f5 f9)))
          // (assert (= s (+ f3 f5 f7)))

          smtAssert(s === f1 + f2 + f3)
          smtAssert(s === f4 + f5 + f6)
          smtAssert(s === f7 + f8 + f9)
          smtAssert(s === f1 + f4 + f7)
          smtAssert(s === f2 + f5 + f8)
          smtAssert(s === f3 + f6 + f9)
          smtAssert(s === f1 + f5 + f9)
          smtAssert(s === f3 + f5 + f7)

          // (check-sat)
          // (get-model)
          smtCheck
        }
