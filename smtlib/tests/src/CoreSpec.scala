// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.smtlib.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.*
import utest.*

import java.lang.foreign.Arena

object CoreSpec extends TestSuite:
  val tests = Tests:
    test("assert"):
      test("Const[Bool]"):
        smtTest("assert true"):
          solver {
            smtAssert(true.B)
          }
        smtTest("assert false"):
          solver {
            smtAssert(false.B)
          }
      test("Ref[Bool]"):
        smtTest("(assert (let ((tmp (a)))", "tmp))"):
          solver {
            val a = SMTFunc(Bool)
            smtAssert(a())
          }
    test("distinct"):
      test("Const[Bool]"):
        smtTest("distinct"):
          solver {
            smtAssert(smtDistinct())
          }
        smtTest("distinct true"):
          solver {
            smtAssert(smtDistinct(true.B))
          }
        smtTest("distinct true true"):
          solver {
            smtAssert(smtDistinct(true.B, true.B))
          }
        smtTest("distinct true false"):
          solver {
            smtAssert(smtDistinct(true.B, false.B))
          }
        smtTest("distinct true true false false"):
          solver {
            smtAssert(smtDistinct(true.B, true.B, false.B, false.B))
          }
      test("Ref[Bool]"):
        smtTest("(let ((tmp (b)))", "(let ((tmp_0 (a)))", "(let ((tmp_1 (distinct tmp_0 tmp)))"):
          solver {
            val a = SMTFunc(Bool)
            val b = SMTFunc(Bool)
            smtAssert(smtDistinct(a(), b()))
          }
    test("reset"):
      smtTest("(reset)\n(reset)"):
        solver {
          smtReset
        }
    test("set-logic"):
      smtTest("(set-logic QF_LIA)"):
        solver {
          smtSetLogic("QF_LIA")
        }
      smtTest("(set-logic XXX)"):
        solver {
          smtSetLogic("XXX")
        }
    test("eq"):
      smtTest("="):
        solver {
          smtAssert(smtEq())
        }
      smtTest("= true"):
        solver {
          smtAssert(smtEq(true.B))
        }
      smtTest("= true true"):
        solver {
          smtAssert(smtEq(true.B, true.B))
        }
      smtTest("= true false"):
        solver {
          smtAssert(smtEq(true.B, false.B))
        }
      smtTest(
        "(declare-fun a () Bool)",
        "(declare-fun b () Int)",
        "(assert (let ((tmp (b)))",
        "        (let ((tmp_0 (a)))",
        "        (let ((tmp_1 (= tmp_0 tmp)))",
        "        tmp_1))))"
      ):
        solver {
          val a = SMTFunc(Bool)
          val b = SMTFunc(SInt)
          smtAssert(smtEq(a(), b()))
        }
      smtTest("= true 1"):
        solver {
          smtAssert(smtEq(true.B, 1.S))
        }
      smtTest(
        "(declare-sort e 1)",
        "(declare-fun a () Bool)",
        "(declare-fun b () Int)",
        "(declare-fun c () (_ BitVec 32))",
        "(declare-fun d () (Int Bool) Bool)",
        "(declare-fun e () (e Int))",
        "(assert (let ((tmp (e)))",
        "        (let ((tmp_0 (d)))",
        "        (let ((tmp_1 (c)))",
        "        (let ((tmp_2 (b)))",
        "        (let ((tmp_3 (a)))",
        "        (let ((tmp_4 (= true 1 #x00000001 tmp_3 tmp_2 tmp_1 tmp_0 tmp)))",
        "        tmp_4)))))))"
      ):
        solver {
          val a = SMTFunc(Bool)
          val b = SMTFunc(SInt)
          val c = SMTFunc(BitVector(true, 32))
          val d = SMTFunc(SMTFunc(Seq(SInt, Bool), Bool))
          val e = SMTFunc(Sort("e", Seq(SInt)))
          smtAssert(smtEq(true.B, 1.S, 1.B(true, 32), a(), b(), c(), d(), e()))
        }
    test("ite"):
      smtTest("ite true true false"):
        solver {
          val cond = true.B
          smtAssert(smtIte(true.B) { true.B } { false.B })
        }
      smtTest(
        "(declare-fun a () Bool)",
        "(declare-fun b () Int)",
        "(declare-fun c () Int)",
        "(assert (let ((tmp (c)))",
        "        (let ((tmp_0 (b)))",
        "        (let ((tmp_1 (a)))",
        "        (let ((tmp_2 (ite tmp_1 tmp_0 tmp)))",
        "        (let ((tmp_3 (= tmp_2 0)))",
        "        tmp_3))))))"
      ):
        solver {
          val a = SMTFunc(Bool)
          val b = SMTFunc(SInt)
          val c = SMTFunc(SInt)
          smtAssert(smtIte(a()) { b() } { c() } === 0.S)
        }
    test("push"):
      smtTest("push 1"):
        solver {
          smtPush(1)
        }
    test("pop"):
      smtTest("pop 1"):
        solver {
          smtPop(1)
        }
    test("check"):
      smtTest("(check-sat)"):
        solver {
          smtCheck
        }
    test("yield"):
      smtTest(""):
        solver {
          smtYield()
        }
