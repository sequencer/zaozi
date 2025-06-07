// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.smtlib.tests

import me.jiuyang.smtlib.{parseSExpr, parseSMT}
import utest.*

object ParseSpec extends TestSuite:
  val tests = Tests:
    test("simple parser"):
      assert(
        parseSExpr(
          """(set-logic QF_UF)
            |(declare-fun x () Int)
            |(assert (> x 5))
            |(check-sat)
            |""".stripMargin
        ).isSuccess
      )
    test("convert to SMT IR"):
      import me.jiuyang.smtlib.SMTCommand.*
      assert(
        parseSMT(
          """(set-logic QF_UF)
            |(declare-fun x () Int)
            |(assert (> x 5))
            |(check-sat)
            |""".stripMargin
        ) == List(
          SetLogic("QF_UF"),
          DeclareFun("x", List(), "Int"),
          Assert(IntCmp(">", Variable("x"), IntConstant(5))),
          Check
        )
      )
