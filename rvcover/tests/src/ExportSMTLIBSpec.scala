// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package rvcover.tests

import org.llvm.circt.scalalib.smt.capi.{*, given}
import org.llvm.circt.scalalib.smt.operation.{*, given}
import org.llvm.mlir.scalalib.{TypeApi as MlirTypeApi, *, given}
import rvcover.default.{*, given}
import rvcover.*
import utest.*

import java.lang.foreign.Arena

object ExportSMTLIBSpec extends TestSuite:
  val tests = Tests:
    test("Check"):
      smtTest(""):
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
        solver { check }
    test("Sudoku"):
      smtTest(""):
        // smt-lib2 format
        solver {

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

          val f1 = smtInt("f1")
          val f2 = smtInt("f2")
          val f3 = smtInt("f3")
          val f4 = smtInt("f4")
          val f5 = smtInt("f5")
          val f6 = smtInt("f6")
          val f7 = smtInt("f7")
          val f8 = smtInt("f8")
          val f9 = smtInt("f9")
          val s  = smtInt("s")

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
            f1 >= 1 & f1 <= 9 & f2 >= 1 & f2 <= 9 & f3 >= 1 & f3 <= 9 & f4 >= 1 & f4 <= 9 &
              f5 >= 1 & f5 <= 9 & f6 >= 1 & f6 <= 9 & f7 >= 1 & f7 <= 9 & f8 >= 1 & f8 <= 9 &
              f9 >= 1 & f9 <= 9 & smtDistinct(Seq(f1, f2, f3, f4, f5, f6, f7, f8, f9))
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

          check
        }
