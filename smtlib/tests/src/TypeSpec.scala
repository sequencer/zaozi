// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.smtlib.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.*
import utest.*

import java.lang.foreign.Arena
import org.llvm.circt.scalalib.smt.tpe.BitVectorType

object TypeSpec extends TestSuite:
  val tests = Tests:
    test("Const"):
      test("BitVector"):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(assert (let ((tmp (a)))",
          "        (let ((tmp_0 (= tmp #x00000000)))",
          "        tmp_0)))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            smtAssert(a() === 0.B(true, 32))
          }
      test("Bool"):
        smtTest("assert true"):
          solver {
            smtAssert(true.B)
          }
        smtTest("assert false"):
          solver {
            smtAssert(false.B)
          }
      test("Int"):
        smtTest(
          "(declare-fun a () Int)",
          "(assert (let ((tmp (a)))",
          "        (let ((tmp_0 (= tmp 1)))",
          "        tmp_0)))"
        ):
          solver {
            val a = SMTFunc(SInt)
            smtAssert(a() === 1.S)
          }
        smtTest(
          "(declare-fun a () Int)",
          "(assert (let ((tmp (a)))",
          "        (let ((tmp_0 (= tmp 0)))",
          "        tmp_0)))"
        ):
          solver {
            val a = SMTFunc(SInt)
            smtAssert(a() === 0.S)
          }
    test("Array"):
      test("declare"):
        smtTest(
          "(declare-fun a () (Array Int Bool))"
        ):
          solver {
            val a = SMTFunc(Array(SInt, Bool))
          }
      test("select"):
        smtTest(
          "(declare-fun a () (Array Int Bool))",
          "(assert (let ((tmp (a)))",
          "        (let ((tmp_0 (select tmp 0)))",
          "        tmp_0)))"
        ):
          solver {
            val a = SMTFunc(Array(SInt, Bool))
            smtAssert(a()(0))
          }
      test("store"):
        smtTest(
          "(declare-fun a () (Array Int Bool))",
          "(assert (let ((tmp (a)))",
          "        (let ((tmp_0 (store tmp 0 true)))",
          "        (let ((tmp_1 (select tmp_0 0)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(Array(SInt, Bool))
            val b = a().update(0, true.B)
            smtAssert(b(0))
          }
      test("broadcast"):
        smtTest(
          "(declare-fun a () (Array Int Bool))",
          "(assert (let ((tmp ((as const (Array Int Bool)) true)))",
          "        (let ((tmp_0 (select tmp 10)))",
          "        tmp_0)))"
        ):
          solver {
            val a = SMTFunc(Array(SInt, Bool))
            val b = a().broadcast(true.B)
            smtAssert(b(10))
          }
    test("BitVector"):
      test("declare"):
        smtTest(
          "(declare-fun a () (_ BitVec 32))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
          }
      test("==="):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(assert (let ((tmp (a)))",
          "        (let ((tmp_0 (= tmp #x00000000)))",
          "        tmp_0)))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            smtAssert(a() === 0.B(true, 32))
          }
      test("=/="):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(assert (let ((tmp (a)))",
          "        (let ((tmp_0 (distinct tmp #x00000000)))",
          "        tmp_0)))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            smtAssert(a() =/= 0.B(true, 32))
          }
      test("+>>"):
        test("Int"):
          smtTest(
            "(declare-fun a () (_ BitVec 32))",
            "(assert (let ((tmp (a)))",
            "        (let ((tmp_0 (bvashr tmp 1)))",
            "        (let ((tmp_1 (= tmp_0 #x00000000)))",
            "        tmp_1))))"
          ):
            solver {
              val a = SMTFunc(BitVector(true, 32))
              smtAssert(a() +>> 1 === 0.B(true, 32))
            }
        test("SInt"):
          smtTest(
            "(declare-fun a () (_ BitVec 32))",
            "(assert (let ((tmp (a)))",
            "        (let ((tmp_0 (bvashr tmp 1)))",
            "        (let ((tmp_1 (= tmp_0 #x00000000)))",
            "        tmp_1))))"
          ):
            solver {
              val a = SMTFunc(BitVector(true, 32))
              smtAssert(a() +>> 1.S === 0.B(true, 32))
            }
      test(">>"):
        test("Int"):
          smtTest(
            "(declare-fun a () (_ BitVec 32))",
            "(assert (let ((tmp (a)))",
            "        (let ((tmp_0 (bvlshr tmp 1)))",
            "        (let ((tmp_1 (= tmp_0 #x00000000)))",
            "        tmp_1))))"
          ):
            solver {
              val a = SMTFunc(BitVector(true, 32))
              smtAssert(a() >> 1 === 0.B(true, 32))
            }
        test("SInt"):
          smtTest(
            "(declare-fun a () (_ BitVec 32))",
            "(assert (let ((tmp (a)))",
            "        (let ((tmp_0 (bvlshr tmp 1)))",
            "        (let ((tmp_1 (= tmp_0 #x00000000)))",
            "        tmp_1))))"
          ):
            solver {
              val a = SMTFunc(BitVector(true, 32))
              smtAssert(a() >> 1.S === 0.B(true, 32))
            }
      test("<<"):
        test("Int"):
          smtTest(
            "(declare-fun a () (_ BitVec 32))",
            "(assert (let ((tmp (a)))",
            "        (let ((tmp_0 (bvshl tmp 1)))",
            "        (let ((tmp_1 (= tmp_0 #x00000000)))",
            "        tmp_1))))"
          ):
            solver {
              val a = SMTFunc(BitVector(true, 32))
              smtAssert(a() << 1 === 0.B(true, 32))
            }
        test("SInt"):
          smtTest(
            "(declare-fun a () (_ BitVec 32))",
            "(assert (let ((tmp (a)))",
            "        (let ((tmp_0 (bvshl tmp 1)))",
            "        (let ((tmp_1 (= tmp_0 #x00000000)))",
            "        tmp_1))))"
          ):
            solver {
              val a = SMTFunc(BitVector(true, 32))
              smtAssert(a() << 1.S === 0.B(true, 32))
            }
      test("+"):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(declare-fun b () (_ BitVec 32))",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (bvadd tmp_0 tmp)))",
          "        (let ((tmp_2 (= tmp_1 #x00000000)))",
          "        tmp_2)))))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            val b = SMTFunc(BitVector(true, 32))
            smtAssert(a() + b() === 0.B(true, 32))
          }
      test("*"):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(declare-fun b () (_ BitVec 32))",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (bvmul tmp_0 tmp)))",
          "        (let ((tmp_2 (= tmp_1 #x00000000)))",
          "        tmp_2)))))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            val b = SMTFunc(BitVector(true, 32))
            smtAssert(a() * b() === 0.B(true, 32))
          }
      test("/"):
        test("sdiv"):
          smtTest(
            "(declare-fun a () (_ BitVec 32))",
            "(declare-fun b () (_ BitVec 32))",
            "(assert (let ((tmp (b)))",
            "        (let ((tmp_0 (a)))",
            "        (let ((tmp_1 (bvsdiv tmp_0 tmp)))",
            "        (let ((tmp_2 (= tmp_1 #x00000000)))",
            "        tmp_2)))))"
          ):
            solver {
              val a = SMTFunc(BitVector(true, 32))
              val b = SMTFunc(BitVector(true, 32))
              smtAssert(a() / b() === 0.B(true, 32))
            }
        test("udiv"):
          smtTest(
            "(declare-fun a () (_ BitVec 32))",
            "(declare-fun b () (_ BitVec 32))",
            "(assert (let ((tmp (b)))",
            "        (let ((tmp_0 (a)))",
            "        (let ((tmp_1 (bvudiv tmp_0 tmp)))",
            "        (let ((tmp_2 (= tmp_1 #x00000000)))",
            "        tmp_2)))))"
          ):
            solver {
              val a = SMTFunc(BitVector(false, 32))
              val b = SMTFunc(BitVector(true, 32))
              smtAssert(a() / b() === 0.B(true, 32))
            }
      test("%"):
        test("srem"):
          smtTest(
            "(declare-fun a () (_ BitVec 32))",
            "(declare-fun b () (_ BitVec 32))",
            "(assert (let ((tmp (b)))",
            "        (let ((tmp_0 (a)))",
            "        (let ((tmp_1 (bvsrem tmp_0 tmp)))",
            "        (let ((tmp_2 (= tmp_1 #x00000000)))",
            "        tmp_2)))))"
          ):
            solver {
              val a = SMTFunc(BitVector(true, 32))
              val b = SMTFunc(BitVector(true, 32))
              smtAssert(a() % b() === 0.B(true, 32))
            }
        test("urem"):
          smtTest(
            "(declare-fun a () (_ BitVec 32))",
            "(declare-fun b () (_ BitVec 32))",
            "(assert (let ((tmp (b)))",
            "        (let ((tmp_0 (a)))",
            "        (let ((tmp_1 (bvurem tmp_0 tmp)))",
            "        (let ((tmp_2 (= tmp_1 #x00000000)))",
            "        tmp_2)))))"
          ):
            solver {
              val a = SMTFunc(BitVector(false, 32))
              val b = SMTFunc(BitVector(true, 32))
              smtAssert(a() % b() === 0.B(true, 32))
            }
      test("&"):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(declare-fun b () (_ BitVec 32))",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (bvand tmp_0 tmp)))",
          "        (let ((tmp_2 (= tmp_1 #x00000000)))",
          "        tmp_2)))))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            val b = SMTFunc(BitVector(true, 32))
            smtAssert((a() & b()) === 0.B(true, 32))
          }
      test("|"):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(declare-fun b () (_ BitVec 32))",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (bvor tmp_0 tmp)))",
          "        (let ((tmp_2 (= tmp_1 #x00000000)))",
          "        tmp_2)))))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            val b = SMTFunc(BitVector(true, 32))
            smtAssert((a() | b()) === 0.B(true, 32))
          }
      test("^"):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(declare-fun b () (_ BitVec 32))",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (bvxor tmp_0 tmp)))",
          "        (let ((tmp_2 (= tmp_1 #x00000000)))",
          "        tmp_2)))))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            val b = SMTFunc(BitVector(true, 32))
            smtAssert((a() ^ b()) === 0.B(true, 32))
          }
      test("++"):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(declare-fun b () (_ BitVec 32))",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (concat tmp_0 tmp)))",
          "        (let ((tmp_2 (= tmp_1 #x0000000000000000)))",
          "        tmp_2)))))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            val b = SMTFunc(BitVector(true, 32))
            smtAssert((a() ++ b()) === 0.B(true, 64))
          }
      test("extract"):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(assert (let ((tmp (a)))",
          "        (let ((tmp_0 ((_ extract 0 0) tmp)))",
          "        (let ((tmp_1 (= tmp_0 #b0)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            smtAssert(a().extract(0, BitVector(true, 1)) === 0.B(true, 1))
          }
      test("repeat"):
        smtTest(
          "(declare-fun a () (_ BitVec 4))",
          "(assert (let ((tmp (a)))",
          "        (let ((tmp_0 ((_ repeat 8) tmp)))",
          "        (let ((tmp_1 (= tmp_0 #x00000000)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 4))
            smtAssert(a().repeat(BitVector(true, 32)) === 0.B(true, 32))
          }
      test("~"):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(assert (let ((tmp (a)))",
          "        (let ((tmp_0 (bvneg tmp)))",
          "        (let ((tmp_1 (= tmp_0 #x00000000)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            smtAssert(~a() === 0.B(true, 32))
          }
      test("!"):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(assert (let ((tmp (a)))",
          "        (let ((tmp_0 (bvnot tmp)))",
          "        (let ((tmp_1 (= tmp_0 #x00000000)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            smtAssert(!a() === 0.B(true, 32))
          }
      test("<"):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(declare-fun b () (_ BitVec 32))",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (bvslt tmp_0 tmp)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            val b = SMTFunc(BitVector(true, 32))
            smtAssert(a() < b())
          }
      test("<="):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(declare-fun b () (_ BitVec 32))",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (bvsle tmp_0 tmp)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            val b = SMTFunc(BitVector(true, 32))
            smtAssert(a() <= b())
          }
      test(">"):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(declare-fun b () (_ BitVec 32))",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (bvsgt tmp_0 tmp)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            val b = SMTFunc(BitVector(true, 32))
            smtAssert(a() > b())
          }
      test(">="):
        smtTest(
          "(declare-fun a () (_ BitVec 32))",
          "(declare-fun b () (_ BitVec 32))",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (bvsge tmp_0 tmp)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(BitVector(true, 32))
            val b = SMTFunc(BitVector(true, 32))
            smtAssert(a() >= b())
          }
    test("Bool"):
      test("declare"):
        smtTest(
          "(declare-fun a () Bool)"
        ):
          solver {
            val a = SMTFunc(Bool)
          }
      test("&"):
        smtTest(
          "(declare-fun a () Bool)",
          "(declare-fun b () Bool)",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (and tmp_0 tmp)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(Bool)
            val b = SMTFunc(Bool)
            smtAssert(a() & b())
          }
      test("|"):
        smtTest(
          "(declare-fun a () Bool)",
          "(declare-fun b () Bool)",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (or tmp_0 tmp)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(Bool)
            val b = SMTFunc(Bool)
            smtAssert(a() | b())
          }
      test("!"):
        smtTest(
          "(declare-fun a () Bool)",
          "(assert (let ((tmp (a)))",
          "        (let ((tmp_0 (not tmp)))",
          "        tmp_0)))"
        ):
          solver {
            val a = SMTFunc(Bool)
            smtAssert(!a())
          }
      test("^"):
        smtTest(
          "(declare-fun a () Bool)",
          "(declare-fun b () Bool)",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (xor tmp_0 tmp)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(Bool)
            val b = SMTFunc(Bool)
            smtAssert(a() ^ b())
          }
      test("==>"):
        smtTest(
          "(declare-fun a () Bool)",
          "(declare-fun b () Bool)",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (=> tmp_0 tmp)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(Bool)
            val b = SMTFunc(Bool)
            smtAssert(a() ==> b())
          }
    test("Int"):
      test("declare"):
        smtTest(
          "(declare-fun a () Int)"
        ):
          solver {
            val a = SMTFunc(SInt)
          }
      test("==="):
        smtTest(
          "(declare-fun a () Int)",
          "(assert (let ((tmp (a)))",
          "        (let ((tmp_0 (= tmp 0)))",
          "        tmp_0)))"
        ):
          solver {
            val a = SMTFunc(SInt)
            smtAssert(a() === 0.S)
          }
      test("=/="):
        smtTest(
          "(declare-fun a () Int)",
          "(assert (let ((tmp (a)))",
          "        (let ((tmp_0 (distinct tmp 0)))",
          "        tmp_0)))"
        ):
          solver {
            val a = SMTFunc(SInt)
            smtAssert(a() =/= 0.S)
          }
      test("+"):
        smtTest(
          "(declare-fun a () Int)",
          "(declare-fun b () Int)",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (+ tmp_0 tmp)))",
          "        (let ((tmp_2 (= tmp_1 0)))",
          "        tmp_2)))))"
        ):
          solver {
            val a = SMTFunc(SInt)
            val b = SMTFunc(SInt)
            smtAssert(a() + b() === 0.S)
          }
      test("-"):
        smtTest(
          "(declare-fun a () Int)",
          "(declare-fun b () Int)",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (- tmp_0 tmp)))",
          "        (let ((tmp_2 (= tmp_1 0)))",
          "        tmp_2)))))"
        ):
          solver {
            val a = SMTFunc(SInt)
            val b = SMTFunc(SInt)
            smtAssert(a() - b() === 0.S)
          }
      test("*"):
        smtTest(
          "(declare-fun a () Int)",
          "(declare-fun b () Int)",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (* tmp_0 tmp)))",
          "        (let ((tmp_2 (= tmp_1 0)))",
          "        tmp_2)))))"
        ):
          solver {
            val a = SMTFunc(SInt)
            val b = SMTFunc(SInt)
            smtAssert(a() * b() === 0.S)
          }
      test("/"):
        smtTest(
          "(declare-fun a () Int)",
          "(declare-fun b () Int)",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (div tmp_0 tmp)))",
          "        (let ((tmp_2 (= tmp_1 0)))",
          "        tmp_2)))))"
        ):
          solver {
            val a = SMTFunc(SInt)
            val b = SMTFunc(SInt)
            smtAssert(a() / b() === 0.S)
          }
      test("%"):
        smtTest(
          "(declare-fun a () Int)",
          "(declare-fun b () Int)",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (mod tmp_0 tmp)))",
          "        (let ((tmp_2 (= tmp_1 0)))",
          "        tmp_2)))))"
        ):
          solver {
            val a = SMTFunc(SInt)
            val b = SMTFunc(SInt)
            smtAssert(a() % b() === 0.S)
          }
      test(">"):
        smtTest(
          "(declare-fun a () Int)",
          "(declare-fun b () Int)",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (> tmp_0 tmp)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(SInt)
            val b = SMTFunc(SInt)
            smtAssert(a() > b())
          }
      test(">="):
        smtTest(
          "(declare-fun a () Int)",
          "(declare-fun b () Int)",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (>= tmp_0 tmp)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(SInt)
            val b = SMTFunc(SInt)
            smtAssert(a() >= b())
          }
      test("<"):
        smtTest(
          "(declare-fun a () Int)",
          "(declare-fun b () Int)",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (< tmp_0 tmp)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(SInt)
            val b = SMTFunc(SInt)
            smtAssert(a() < b())
          }
      test("<="):
        smtTest(
          "(declare-fun a () Int)",
          "(declare-fun b () Int)",
          "(assert (let ((tmp (b)))",
          "        (let ((tmp_0 (a)))",
          "        (let ((tmp_1 (<= tmp_0 tmp)))",
          "        tmp_1))))"
        ):
          solver {
            val a = SMTFunc(SInt)
            val b = SMTFunc(SInt)
            smtAssert(a() <= b())
          }
    test("SMTFunc"):
      test("declare"):
        smtTest(
          "(declare-fun f () (Int Bool) Bool)"
        ):
          solver {
            val f = SMTFunc(SMTFunc(Seq(SInt, Bool), Bool))
          }
      test("apply"):
        smtTest(
          "(declare-fun f () (Int Bool) Bool)",
          "(assert (let ((tmp (f 0 true)))",
          "        (let ((tmp_0 (tmp)))",
          "        tmp_0)))"
        ):
          solver {
            val f = SMTFunc(SMTFunc(Seq(SInt, Bool), Bool))
            val a = f(0.S, true.B)
            smtAssert(a())
          }
    test("Sort"):
      test("declare"):
        smtTest("(declare-fun a () (b Int))"):
          solver {
            val a = SMTFunc(Sort("b", Seq(SInt)))
          }
