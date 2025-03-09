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

          val IntType = summon[TypeApi].getInt()
          val f1      = declareFun("f1", IntType)
          val f2      = declareFun("f2", IntType)
          val f3      = declareFun("f3", IntType)
          val f4      = declareFun("f4", IntType)
          val f5      = declareFun("f5", IntType)
          val f6      = declareFun("f6", IntType)
          val f7      = declareFun("f7", IntType)
          val f8      = declareFun("f8", IntType)
          val f9      = declareFun("f9", IntType)
          val s       = declareFun("s", IntType)

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

          // get constants
          val i11      = intCmp(f1, getInt(1), "ge")
          val i19      = intCmp(f1, getInt(9), "le")
          val i21      = intCmp(f2, getInt(1), "ge")
          val i29      = intCmp(f2, getInt(9), "le")
          val i31      = intCmp(f3, getInt(1), "ge")
          val i39      = intCmp(f3, getInt(9), "le")
          val i41      = intCmp(f4, getInt(1), "ge")
          val i49      = intCmp(f4, getInt(9), "le")
          val i51      = intCmp(f5, getInt(1), "ge")
          val i59      = intCmp(f5, getInt(9), "le")
          val i61      = intCmp(f6, getInt(1), "ge")
          val i69      = intCmp(f6, getInt(9), "le")
          val i71      = intCmp(f7, getInt(1), "ge")
          val i79      = intCmp(f7, getInt(9), "le")
          val i81      = intCmp(f8, getInt(1), "ge")
          val i89      = intCmp(f8, getInt(9), "le")
          val i91      = intCmp(f9, getInt(1), "ge")
          val i99      = intCmp(f9, getInt(9), "le")
          val distinct = smtDistinct(Seq(f1, f2, f3, f4, f5, f6, f7, f8, f9))

          val and0 =
            and(Seq(i11, i19, i21, i29, i31, i39, i41, i49, i51, i59, i61, i69, i71, i79, i81, i89, i91, i99, distinct))

          smtAssert(and0)

          // (assert (= s ( f1 f2 f3)))
          // (assert (= s (+ f4 f5 f6)))
          // (assert (= s (+ f7 f8 f9)))
          // (assert (= s (+ f1 f4 f7)))
          // (assert (= s (+ f2 f5 f8)))
          // (assert (= s (+ f3 f6 f9)))
          // (assert (= s (+ f1 f5 f9)))
          // (assert (= s (+ f3 f5 f7)))

          val s123 = intAdd(Seq(f1, f2, f3))
          val s456 = intAdd(Seq(f4, f5, f6))
          val s789 = intAdd(Seq(f7, f8, f9))
          val s147 = intAdd(Seq(f1, f4, f7))
          val s258 = intAdd(Seq(f2, f5, f8))
          val s369 = intAdd(Seq(f3, f6, f9))
          val s159 = intAdd(Seq(f1, f5, f9))
          val s357 = intAdd(Seq(f3, f5, f7))

          val eq0 = smtEq(Seq(s, s123, s456, s789, s147, s258, s369, s159, s357))

          smtAssert(eq0)

          check

          // val f[9], s
          // assert(for i in f: 1 <= i <= 9)
          // assert(distinct f)
          // assert(s == f[1] + f[2] + f[3] == f[4] + f[5] + f[6] == f[7] + f[8] + f[9] == f[1] + f[4] + f[7] == f[2] + f[5] + f[8] == f[3] + f[6] + f[9] == f[1] + f[5] + f[9] == f[3] + f[5] + f[7])
          // check-sat
        }
