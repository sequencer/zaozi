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
        context.loadFirrtlDialect()
        context.loadSmtDialect()
        given Context       = context
        val unknownLocation = summon[LocationApi].locationUnknownGet
        test("Create MlirModule"):
          given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(unknownLocation)
          // TODO: use circuit api by default to include smt dialect
          test("Create Circuit"):
            val circuit: Circuit = summon[CircuitApi].op("Passthrough")
            circuit.appendToModule()
        test("Create CirctModule"):
          val api = summon[FirrtlBundleFieldApi]
          val module: Module = summon[ModuleApi].op(
            "DummyModule",
            unknownLocation,
            FirrtlConvention.Scalarized,
            Seq(
              (api.createFirrtlBundleField("i", true, 32.getUInt), unknownLocation),
              (api.createFirrtlBundleField("o", false, 32.getUInt), unknownLocation)
            ),
            Seq.empty
          )
          given Module = module
          given Block  = module.block
          test("Smt"):
            val bool0   = summon[WireApi].op(
              name = "bool0",
              location = unknownLocation,
              nameKind = FirrtlNameKind.Droppable,
              tpe = 0.getUInt
            )
            val bool1   = summon[WireApi].op(
              name = "bool1",
              location = unknownLocation,
              nameKind = FirrtlNameKind.Droppable,
              tpe = 1.getUInt
            )
            test("And"):
              summon[AndApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()