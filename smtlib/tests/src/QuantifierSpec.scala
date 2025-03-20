// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.smtlib.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.*
import utest.*

import java.lang.foreign.Arena

object QuantifierSpec extends TestSuite:
  val tests = Tests:
    test("Exist"):
      smtTest(
        "(assert (let ((tmp (exists ()",
        "                           ( ! (let ((tmp_0 (x)))",
        "                           (let ((tmp_1 (= tmp_0 1)))",
        "                           tmp_1)) :weight 1))))",
        "        tmp))"
      ):
        solver {
          smtAssert(smtExists(1, false, Seq.empty) {
            val x = SMTFunc(SInt)
            smtYield(x() === 1.S)
          })
        }
    test("Forall"):
      smtTest(
        "(declare-fun x () Int)",
        "(assert (let ((tmp (forall ()",
        "                           ( ! (let ((tmp_0 (x)))",
        "                           (let ((tmp_1 (= tmp_0 1)))",
        "                           tmp_1)) :weight 1))))",
        "        tmp))"
      ):
        solver {
          smtAssert(smtForall(1, false, Seq.empty) {
            val x = SMTFunc(SInt)
            smtYield(x() === 1.S)
          })
        }
