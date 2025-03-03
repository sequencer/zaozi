// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.tests

import org.llvm.circt.scalalib.smt.capi.given_DialectHandleApi
import org.llvm.circt.scalalib.smt.operation.{*, given}
import org.llvm.mlir.scalalib.{Module as MlirModule, ModuleApi as MlirModuleApi, *, given}
import utest.*

import java.lang.foreign.Arena

object SMTSpec extends TestSuite:
  val tests = Tests:
    test("AndApi"):
      smtTest():
        val unknownLocation = summon[LocationApi].locationUnknownGet
        val bool0 = summon[BoolConstantApi].op(false, location = unknownLocation)
        val bool1 = summon[BoolConstantApi].op(true, location = unknownLocation)
        summon[AndApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()