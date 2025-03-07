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
        val unknownLocation = summon[LocationApi].locationUnknownGet

        // %0 = smt.check sat {
        //   %c1 = llvm.mlir.constant(1 : i32) : i32
        //   smt.yield %c1 : i32
        // } unknown {
        //   %c0 = llvm.mlir.constant(0 : i32) : i32
        //   smt.yield %c0 : i32
        // } unsat {
        //   %c-1 = llvm.mlir.constant(-1 : i32) : i32
        //   smt.yield %c-1 : i32
        // } -> i32

        val result = check {
          // sat
          val int1 = getInt(1)
          smtYield(Seq(int1))
        } {
          // unknown
          val int0 = getInt(0)
          smtYield(Seq(int0))
        } {
          // unsat
          val int2 = getInt(2)
          smtYield(Seq(int2))
        }
