// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.smtlib.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.*
import utest.*

import java.lang.foreign.Arena

object TypeSpec extends TestSuite:
  val tests = Tests:
    test("Const"):
      test("BitVector"):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(assert (let ((tmp (= a #x00000000)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            smtAssert(a === 0.B(true, 32))
          }
      test("Bool"):
        smtTest(
          "(assert true)"
        ):
          solver {
            smtAssert(true.B)
          }
        smtTest(
          "(assert false)"
        ):
          solver {
            smtAssert(false.B)
          }
        smtTest(
          "(declare-const a Bool)",
          "(assert (let ((tmp (= a true)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(Bool)
            smtAssert(a === true.B)
          }
        smtTest(
          "(declare-const a Bool)",
          "(assert (let ((tmp (distinct a true)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(Bool)
            smtAssert(a =/= true.B)
          }
      test("Int"):
        smtTest(
          "(declare-const a Int)",
          "(assert (let ((tmp (= a 1)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(SInt)
            smtAssert(a === 1.S)
          }
        smtTest(
          "(declare-const a Int)",
          "(assert (let ((tmp (= a 0)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(SInt)
            smtAssert(a === 0.S)
          }
    test("Array"):
      test("declare"):
        smtTest(
          "(declare-const a (Array Int Bool))"
        ):
          solver {
            val a = smtValue(Array(SInt, Bool))
          }
      test("select"):
        smtTest(
          "(declare-const a (Array Int Bool))",
          "(assert (let ((tmp (select a 0)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(Array(SInt, Bool))
            smtAssert(a(0))
          }
      test("store"):
        smtTest(
          "(declare-const a (Array Int Bool))",
          "(assert (let ((tmp (store a 0 true)))",
          "        (let ((tmp_0 (select tmp 0)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(Array(SInt, Bool))
            val b = a.update(0, true.B)
            smtAssert(b(0))
          }
      test("broadcast"):
        smtTest(
          "(declare-const a (Array Int Bool))",
          "(assert (let ((tmp ((as const (Array Int Bool)) true)))",
          "        (let ((tmp_0 (select tmp 10)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(Array(SInt, Bool))
            val b = a.broadcast(true.B)
            smtAssert(b(10))
          }
    test("BitVector"):
      test("declare"):
        smtTest(
          "(declare-const a (_ BitVec 32))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
          }
      test("==="):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(assert (let ((tmp (= a #x00000000)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            smtAssert(a === 0.B(true, 32))
          }
      test("=/="):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(assert (let ((tmp (distinct a #x00000000)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            smtAssert(a =/= 0.B(true, 32))
          }
      test("+>>"):
        test("Int"):
          smtTest(
            "(declare-const a (_ BitVec 32))",
            "(assert (let ((tmp (bvashr a #x00000001)))",
            "        (let ((tmp_0 (= tmp #x00000000)))",
            "        tmp_0)))"
          ):
            solver {
              val a = smtValue(BitVector(true, 32))
              smtAssert(a +>> 1 === 0.B(true, 32))
            }
        test("SInt"):
          smtTest(
            "(declare-const a (_ BitVec 32))",
            "(assert (let ((tmp (bvashr a #x00000001)))",
            "        (let ((tmp_0 (= tmp #x00000000)))",
            "        tmp_0)))"
          ):
            solver {
              val a = smtValue(BitVector(true, 32))
              smtAssert(a +>> 1.B(true, 32) === 0.B(true, 32))
            }
      test(">>"):
        test("Int"):
          smtTest(
            "(declare-const a (_ BitVec 32))",
            "(assert (let ((tmp (bvlshr a #x00000001)))",
            "        (let ((tmp_0 (= tmp #x00000000)))",
            "        tmp_0)))"
          ):
            solver {
              val a = smtValue(BitVector(true, 32))
              smtAssert(a >> 1 === 0.B(true, 32))
            }
        test("SInt"):
          smtTest(
            "(declare-const a (_ BitVec 32))",
            "(assert (let ((tmp (bvlshr a #x00000001)))",
            "        (let ((tmp_0 (= tmp #x00000000)))",
            "        tmp_0)))"
          ):
            solver {
              val a = smtValue(BitVector(true, 32))
              smtAssert(a >> 1.B(true, 32) === 0.B(true, 32))
            }
      test("<<"):
        test("Int"):
          smtTest(
            "(declare-const a (_ BitVec 32))",
            "(assert (let ((tmp (bvshl a #x00000001)))",
            "        (let ((tmp_0 (= tmp #x00000000)))",
            "        tmp_0)))"
          ):
            solver {
              val a = smtValue(BitVector(true, 32))
              smtAssert(a << 1 === 0.B(true, 32))
            }
        test("SInt"):
          smtTest(
            "(declare-const a (_ BitVec 32))",
            "(assert (let ((tmp (bvshl a #x00000001)))",
            "        (let ((tmp_0 (= tmp #x00000000)))",
            "        tmp_0)))"
          ):
            solver {
              val a = smtValue(BitVector(true, 32))
              smtAssert(a << 1.B(true, 32) === 0.B(true, 32))
            }
      test("+"):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(declare-const b (_ BitVec 32))",
          "(assert (let ((tmp (bvadd a b)))",
          "        (let ((tmp_0 (= tmp #x00000000)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            val b = smtValue(BitVector(true, 32))
            smtAssert(a + b === 0.B(true, 32))
          }
      test("*"):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(declare-const b (_ BitVec 32))",
          "(assert (let ((tmp (bvmul a b)))",
          "        (let ((tmp_0 (= tmp #x00000000)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            val b = smtValue(BitVector(true, 32))
            smtAssert(a * b === 0.B(true, 32))
          }
      test("/"):
        test("sdiv"):
          smtTest(
            "(declare-const a (_ BitVec 32))",
            "(declare-const b (_ BitVec 32))",
            "(assert (let ((tmp (bvsdiv a b)))",
            "        (let ((tmp_0 (= tmp #x00000000)))",
            "        tmp_0)))"
          ):
            solver {
              val a = smtValue(BitVector(true, 32))
              val b = smtValue(BitVector(true, 32))
              smtAssert(a / b === 0.B(true, 32))
            }
        test("udiv"):
          smtTest(
            "(declare-const a (_ BitVec 32))",
            "(declare-const b (_ BitVec 32))",
            "(assert (let ((tmp (bvudiv a b)))",
            "        (let ((tmp_0 (= tmp #x00000000)))",
            "        tmp_0)))"
          ):
            solver {
              val a = smtValue(BitVector(false, 32))
              val b = smtValue(BitVector(true, 32))
              smtAssert(a / b === 0.B(true, 32))
            }
      test("%"):
        test("srem"):
          smtTest(
            "(declare-const a (_ BitVec 32))",
            "(declare-const b (_ BitVec 32))",
            "(assert (let ((tmp (bvsrem a b)))",
            "        (let ((tmp_0 (= tmp #x00000000)))",
            "        tmp_0)))"
          ):
            solver {
              val a = smtValue(BitVector(true, 32))
              val b = smtValue(BitVector(true, 32))
              smtAssert(a % b === 0.B(true, 32))
            }
        test("urem"):
          smtTest(
            "(declare-const a (_ BitVec 32))",
            "(declare-const b (_ BitVec 32))",
            "(assert (let ((tmp (bvurem a b)))",
            "        (let ((tmp_0 (= tmp #x00000000)))",
            "        tmp_0)))"
          ):
            solver {
              val a = smtValue(BitVector(false, 32))
              val b = smtValue(BitVector(true, 32))
              smtAssert(a % b === 0.B(true, 32))
            }
      test("&"):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(declare-const b (_ BitVec 32))",
          "(assert (let ((tmp (bvand a b)))",
          "        (let ((tmp_0 (= tmp #x00000000)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            val b = smtValue(BitVector(true, 32))
            smtAssert((a & b) === 0.B(true, 32))
          }
      test("|"):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(declare-const b (_ BitVec 32))",
          "(assert (let ((tmp (bvor a b)))",
          "        (let ((tmp_0 (= tmp #x00000000)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            val b = smtValue(BitVector(true, 32))
            smtAssert((a | b) === 0.B(true, 32))
          }
      test("^"):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(declare-const b (_ BitVec 32))",
          "(assert (let ((tmp (bvxor a b)))",
          "        (let ((tmp_0 (= tmp #x00000000)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            val b = smtValue(BitVector(true, 32))
            smtAssert((a ^ b) === 0.B(true, 32))
          }
      test("++"):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(declare-const b (_ BitVec 32))",
          "(assert (let ((tmp (concat a b)))",
          "        (let ((tmp_0 (= tmp #x0000000000000000)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            val b = smtValue(BitVector(true, 32))
            smtAssert((a ++ b) === 0.B(true, 64))
          }
      test("extract"):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(assert (let ((tmp ((_ extract 0 0) a)))",
          "        (let ((tmp_0 (= tmp #b0)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            smtAssert(a.extract(0, BitVector(true, 1)) === 0.B(true, 1))
          }
      test("repeat"):
        smtTest(
          "(declare-const a (_ BitVec 4))",
          "(assert (let ((tmp ((_ repeat 8) a)))",
          "        (let ((tmp_0 (= tmp #x00000000)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(BitVector(true, 4))
            smtAssert(a.repeat(BitVector(true, 32)) === 0.B(true, 32))
          }
      test("~"):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(assert (let ((tmp (bvneg a)))",
          "        (let ((tmp_0 (= tmp #x00000000)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            smtAssert(~a === 0.B(true, 32))
          }
      test("!"):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(assert (let ((tmp (bvnot a)))",
          "        (let ((tmp_0 (= tmp #x00000000)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            smtAssert(!a === 0.B(true, 32))
          }
      test("<"):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(declare-const b (_ BitVec 32))",
          "(assert (let ((tmp (bvslt a b)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            val b = smtValue(BitVector(true, 32))
            smtAssert(a < b)
          }
      test("<="):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(declare-const b (_ BitVec 32))",
          "(assert (let ((tmp (bvsle a b)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            val b = smtValue(BitVector(true, 32))
            smtAssert(a <= b)
          }
      test(">"):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(declare-const b (_ BitVec 32))",
          "(assert (let ((tmp (bvsgt a b)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            val b = smtValue(BitVector(true, 32))
            smtAssert(a > b)
          }
      test(">="):
        smtTest(
          "(declare-const a (_ BitVec 32))",
          "(declare-const b (_ BitVec 32))",
          "(assert (let ((tmp (bvsge a b)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(BitVector(true, 32))
            val b = smtValue(BitVector(true, 32))
            smtAssert(a >= b)
          }
    test("Bool"):
      test("declare"):
        smtTest(
          "(declare-const a Bool)"
        ):
          solver {
            val a = smtValue(Bool)
          }
      test("&"):
        smtTest(
          "(declare-const a Bool)",
          "(declare-const b Bool)",
          "(assert (let ((tmp (and a b)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(Bool)
            val b = smtValue(Bool)
            smtAssert(a & b)
          }
      test("|"):
        smtTest(
          "(declare-const a Bool)",
          "(declare-const b Bool)",
          "(assert (let ((tmp (or a b)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(Bool)
            val b = smtValue(Bool)
            smtAssert(a | b)
          }
      test("!"):
        smtTest(
          "(declare-const a Bool)",
          "(assert (let ((tmp (not a)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(Bool)
            smtAssert(!a)
          }
      test("^"):
        smtTest(
          "(declare-const a Bool)",
          "(declare-const b Bool)",
          "(assert (let ((tmp (xor a b)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(Bool)
            val b = smtValue(Bool)
            smtAssert(a ^ b)
          }
      test("==>"):
        smtTest(
          "(declare-const a Bool)",
          "(declare-const b Bool)",
          "(assert (let ((tmp (=> a b)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(Bool)
            val b = smtValue(Bool)
            smtAssert(a ==> b)
          }
    test("Int"):
      test("declare"):
        smtTest(
          "(declare-const a Int)"
        ):
          solver {
            val a = smtValue(SInt)
          }
      test("==="):
        smtTest(
          "(declare-const a Int)",
          "(assert (let ((tmp (= a 0)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(SInt)
            smtAssert(a === 0.S)
          }
      test("=/="):
        smtTest(
          "(declare-const a Int)",
          "(assert (let ((tmp (distinct a 0)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(SInt)
            smtAssert(a =/= 0.S)
          }
      test("+"):
        smtTest(
          "(declare-const a Int)",
          "(declare-const b Int)",
          "(assert (let ((tmp (+ a b)))",
          "        (let ((tmp_0 (= tmp 0)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(SInt)
            val b = smtValue(SInt)
            smtAssert(a + b === 0.S)
          }
      test("-"):
        smtTest(
          "(declare-const a Int)",
          "(declare-const b Int)",
          "(assert (let ((tmp (- a b)))",
          "        (let ((tmp_0 (= tmp 0)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(SInt)
            val b = smtValue(SInt)
            smtAssert(a - b === 0.S)
          }
      test("*"):
        smtTest(
          "(declare-const a Int)",
          "(declare-const b Int)",
          "(assert (let ((tmp (* a b)))",
          "        (let ((tmp_0 (= tmp 0)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(SInt)
            val b = smtValue(SInt)
            smtAssert(a * b === 0.S)
          }
      test("/"):
        smtTest(
          "(declare-const a Int)",
          "(declare-const b Int)",
          "(assert (let ((tmp (div a b)))",
          "        (let ((tmp_0 (= tmp 0)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(SInt)
            val b = smtValue(SInt)
            smtAssert(a / b === 0.S)
          }
      test("%"):
        smtTest(
          "(declare-const a Int)",
          "(declare-const b Int)",
          "(assert (let ((tmp (mod a b)))",
          "        (let ((tmp_0 (= tmp 0)))",
          "        tmp_0)))"
        ):
          solver {
            val a = smtValue(SInt)
            val b = smtValue(SInt)
            smtAssert(a % b === 0.S)
          }
      test(">"):
        smtTest(
          "(declare-const a Int)",
          "(declare-const b Int)",
          "(assert (let ((tmp (> a b)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(SInt)
            val b = smtValue(SInt)
            smtAssert(a > b)
          }
      test(">="):
        smtTest(
          "(declare-const a Int)",
          "(declare-const b Int)",
          "(assert (let ((tmp (>= a b)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(SInt)
            val b = smtValue(SInt)
            smtAssert(a >= b)
          }
      test("<"):
        smtTest(
          "(declare-const a Int)",
          "(declare-const b Int)",
          "(assert (let ((tmp (< a b)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(SInt)
            val b = smtValue(SInt)
            smtAssert(a < b)
          }
      test("<="):
        smtTest(
          "(declare-const a Int)",
          "(declare-const b Int)",
          "(assert (let ((tmp (<= a b)))",
          "        tmp))"
        ):
          solver {
            val a = smtValue(SInt)
            val b = smtValue(SInt)
            smtAssert(a <= b)
          }
    test("SMTFunc"):
      test("declare"):
        smtTest(
          "(declare-fun f (Int Bool) Bool)"
        ):
          solver {
            val f = smtValue(SMTFunc(Seq(SInt, Bool), Bool))
          }
      test("apply"):
        smtTest(
          "(declare-fun f (Int Bool) Bool)",
          "(assert (let ((tmp (f 0 true)))",
          "        tmp))"
        ):
          solver {
            val f = smtValue(SMTFunc(Seq(SInt, Bool), Bool))
            val a = f(0.S, true.B)
            smtAssert(a)
          }
    test("Sort"):
      test("declare"):
        smtTest(
          "(declare-sort b 1)",
          "(declare-const a (b Int))"
        ):
          solver {
            val a = smtValue(Sort("b", Seq(SInt)))
          }
