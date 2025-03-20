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
        "(declare-fun f1 () Int)",
        "(declare-fun f2 () Int)",
        "(declare-fun f3 () Int)",
        "(declare-fun f4 () Int)",
        "(declare-fun f5 () Int)",
        "(declare-fun f6 () Int)",
        "(declare-fun f7 () Int)",
        "(declare-fun f8 () Int)",
        "(declare-fun f9 () Int)",
        "(declare-fun s () Int)",
        "(assert (let ((tmp (distinct f1 f2 f3 f4 f5 f6 f7 f8 f9)))",
        "        (let ((tmp_0 (f9)))",
        "        (let ((tmp_1 (<= tmp_0 9)))",
        "        (let ((tmp_2 (f9)))",
        "        (let ((tmp_3 (>= tmp_2 1)))",
        "        (let ((tmp_4 (f8)))",
        "        (let ((tmp_5 (<= tmp_4 9)))",
        "        (let ((tmp_6 (f8)))",
        "        (let ((tmp_7 (>= tmp_6 1)))",
        "        (let ((tmp_8 (f7)))",
        "        (let ((tmp_9 (<= tmp_8 9)))",
        "        (let ((tmp_10 (f7)))",
        "        (let ((tmp_11 (>= tmp_10 1)))",
        "        (let ((tmp_12 (f6)))",
        "        (let ((tmp_13 (<= tmp_12 9)))",
        "        (let ((tmp_14 (f6)))",
        "        (let ((tmp_15 (>= tmp_14 1)))",
        "        (let ((tmp_16 (f5)))",
        "        (let ((tmp_17 (<= tmp_16 9)))",
        "        (let ((tmp_18 (f5)))",
        "        (let ((tmp_19 (>= tmp_18 1)))",
        "        (let ((tmp_20 (f4)))",
        "        (let ((tmp_21 (<= tmp_20 9)))",
        "        (let ((tmp_22 (f4)))",
        "        (let ((tmp_23 (>= tmp_22 1)))",
        "        (let ((tmp_24 (f3)))",
        "        (let ((tmp_25 (<= tmp_24 9)))",
        "        (let ((tmp_26 (f3)))",
        "        (let ((tmp_27 (>= tmp_26 1)))",
        "        (let ((tmp_28 (f2)))",
        "        (let ((tmp_29 (<= tmp_28 9)))",
        "        (let ((tmp_30 (f2)))",
        "        (let ((tmp_31 (>= tmp_30 1)))",
        "        (let ((tmp_32 (f1)))",
        "        (let ((tmp_33 (<= tmp_32 9)))",
        "        (let ((tmp_34 (f1)))",
        "        (let ((tmp_35 (>= tmp_34 1)))",
        "        (let ((tmp_36 (and tmp_35 tmp_33)))",
        "        (let ((tmp_37 (and tmp_36 tmp_31)))",
        "        (let ((tmp_38 (and tmp_37 tmp_29)))",
        "        (let ((tmp_39 (and tmp_38 tmp_27)))",
        "        (let ((tmp_40 (and tmp_39 tmp_25)))",
        "        (let ((tmp_41 (and tmp_40 tmp_23)))",
        "        (let ((tmp_42 (and tmp_41 tmp_21)))",
        "        (let ((tmp_43 (and tmp_42 tmp_19)))",
        "        (let ((tmp_44 (and tmp_43 tmp_17)))",
        "        (let ((tmp_45 (and tmp_44 tmp_15)))",
        "        (let ((tmp_46 (and tmp_45 tmp_13)))",
        "        (let ((tmp_47 (and tmp_46 tmp_11)))",
        "        (let ((tmp_48 (and tmp_47 tmp_9)))",
        "        (let ((tmp_49 (and tmp_48 tmp_7)))",
        "        (let ((tmp_50 (and tmp_49 tmp_5)))",
        "        (let ((tmp_51 (and tmp_50 tmp_3)))",
        "        (let ((tmp_52 (and tmp_51 tmp_1)))",
        "        (let ((tmp_53 (and tmp_52 tmp)))",
        "        tmp_53))))))))))))))))))))))))))))))))))))))))))))))))))))))))",
        "(assert (let ((tmp_54 (f3)))",
        "        (let ((tmp_55 (f2)))",
        "        (let ((tmp_56 (f1)))",
        "        (let ((tmp_57 (+ tmp_56 tmp_55)))",
        "        (let ((tmp_58 (+ tmp_57 tmp_54)))",
        "        (let ((tmp_59 (s)))",
        "        (let ((tmp_60 (= tmp_59 tmp_58)))",
        "        tmp_60))))))))",
        "(assert (let ((tmp_61 (f6)))",
        "        (let ((tmp_62 (f5)))",
        "        (let ((tmp_63 (f4)))",
        "        (let ((tmp_64 (+ tmp_63 tmp_62)))",
        "        (let ((tmp_65 (+ tmp_64 tmp_61)))",
        "        (let ((tmp_66 (s)))",
        "        (let ((tmp_67 (= tmp_66 tmp_65)))",
        "        tmp_67))))))))",
        "(assert (let ((tmp_68 (f9)))",
        "        (let ((tmp_69 (f8)))",
        "        (let ((tmp_70 (f7)))",
        "        (let ((tmp_71 (+ tmp_70 tmp_69)))",
        "        (let ((tmp_72 (+ tmp_71 tmp_68)))",
        "        (let ((tmp_73 (s)))",
        "        (let ((tmp_74 (= tmp_73 tmp_72)))",
        "        tmp_74))))))))",
        "(assert (let ((tmp_75 (f7)))",
        "        (let ((tmp_76 (f4)))",
        "        (let ((tmp_77 (f1)))",
        "        (let ((tmp_78 (+ tmp_77 tmp_76)))",
        "        (let ((tmp_79 (+ tmp_78 tmp_75)))",
        "        (let ((tmp_80 (s)))",
        "        (let ((tmp_81 (= tmp_80 tmp_79)))",
        "        tmp_81))))))))",
        "(assert (let ((tmp_82 (f8)))",
        "        (let ((tmp_83 (f5)))",
        "        (let ((tmp_84 (f2)))",
        "        (let ((tmp_85 (+ tmp_84 tmp_83)))",
        "        (let ((tmp_86 (+ tmp_85 tmp_82)))",
        "        (let ((tmp_87 (s)))",
        "        (let ((tmp_88 (= tmp_87 tmp_86)))",
        "        tmp_88))))))))",
        "(assert (let ((tmp_89 (f9)))",
        "        (let ((tmp_90 (f6)))",
        "        (let ((tmp_91 (f3)))",
        "        (let ((tmp_92 (+ tmp_91 tmp_90)))",
        "        (let ((tmp_93 (+ tmp_92 tmp_89)))",
        "        (let ((tmp_94 (s)))",
        "        (let ((tmp_95 (= tmp_94 tmp_93)))",
        "        tmp_95))))))))",
        "(assert (let ((tmp_96 (f9)))",
        "        (let ((tmp_97 (f5)))",
        "        (let ((tmp_98 (f1)))",
        "        (let ((tmp_99 (+ tmp_98 tmp_97)))",
        "        (let ((tmp_100 (+ tmp_99 tmp_96)))",
        "        (let ((tmp_101 (s)))",
        "        (let ((tmp_102 (= tmp_101 tmp_100)))",
        "        tmp_102))))))))",
        "(assert (let ((tmp_103 (f7)))",
        "        (let ((tmp_104 (f5)))",
        "        (let ((tmp_105 (f3)))",
        "        (let ((tmp_106 (+ tmp_105 tmp_104)))",
        "        (let ((tmp_107 (+ tmp_106 tmp_103)))",
        "        (let ((tmp_108 (s)))",
        "        (let ((tmp_109 (= tmp_108 tmp_107)))",
        "        tmp_109))))))))"
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

          val f1 = SMTFunc(SInt)
          val f2 = SMTFunc(SInt)
          val f3 = SMTFunc(SInt)
          val f4 = SMTFunc(SInt)
          val f5 = SMTFunc(SInt)
          val f6 = SMTFunc(SInt)
          val f7 = SMTFunc(SInt)
          val f8 = SMTFunc(SInt)
          val f9 = SMTFunc(SInt)
          val s  = SMTFunc(SInt)

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
            f1() >= 1.S & f1() <= 9.S & f2() >= 1.S & f2() <= 9.S & f3() >= 1.S & f3() <= 9.S & f4() >= 1.S & f4() <= 9.S &
              f5() >= 1.S & f5() <= 9.S & f6() >= 1.S & f6() <= 9.S & f7() >= 1.S & f7() <= 9.S & f8() >= 1.S & f8() <= 9.S &
              f9() >= 1.S & f9() <= 9.S & smtDistinct(f1, f2, f3, f4, f5, f6, f7, f8, f9)
          )

          // (assert (= s ( f1 f2 f3)))
          // (assert (= s (+ f4 f5 f6)))
          // (assert (= s (+ f7 f8 f9)))
          // (assert (= s (+ f1 f4 f7)))
          // (assert (= s (+ f2 f5 f8)))
          // (assert (= s (+ f3 f6 f9)))
          // (assert (= s (+ f1 f5 f9)))
          // (assert (= s (+ f3 f5 f7)))

          smtAssert(s() === f1() + f2() + f3())
          smtAssert(s() === f4() + f5() + f6())
          smtAssert(s() === f7() + f8() + f9())
          smtAssert(s() === f1() + f4() + f7())
          smtAssert(s() === f2() + f5() + f8())
          smtAssert(s() === f3() + f6() + f9())
          smtAssert(s() === f1() + f5() + f9())
          smtAssert(s() === f3() + f5() + f7())

          // (check-sat)
          // (get-model)
          smtCheck
        }
