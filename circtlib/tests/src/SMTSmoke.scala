// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.circtlib.tests

import org.llvm.circt.scalalib.firrtl.capi.{
  given_DialectHandleApi,
  given_FirrtlBundleFieldApi,
  given_FirrtlDirectionApi,
  given_TypeApi,
  FirrtlBundleFieldApi,
  FirrtlConvention,
  FirrtlNameKind,
  TypeApi
}
import org.llvm.circt.scalalib.firrtl.operation.{*, given}
import org.llvm.circt.scalalib.smt.operation.{*, given}
import org.llvm.mlir.scalalib.{given_ModuleApi, Module as MlirModule, ModuleApi as MlirModuleApi, *, given}
import utest.*

import java.lang.foreign.Arena

object SMTSmoke extends TestSuite:
  val tests = Tests:
    test("Load Panama Context"):
      val arena   = Arena.ofConfined()
      given Arena = arena
      test("Load Dialect"):
        val context         = summon[ContextApi].contextCreate
        context.loadSmtDialect()
        given Context       = context
        val unknownLocation = summon[LocationApi].locationUnknownGet