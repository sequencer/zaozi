// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.smtlib.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.*
import utest.*

import java.lang.foreign.Arena

object Z3Demo extends TestSuite:
  val tests = Tests:
    smtToZ3llvmTest(""):
      smtAssert(true.B)
