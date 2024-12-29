// SPDX-License-Identifier: Apache-2.0
package me.jiuyang.zaozi.zaozilib.tests

import org.llvm.circt.scalalib.{FirrtlBundleFieldApi, TypeApi, Circuit as CirctCircuit, Module as CirctModule, given}
import org.llvm.mlir.scalalib.{Context, ContextApi, LocationApi, ModuleApi, Module as MlirModule, given}
import utest.*

import java.lang.foreign.Arena

object Smoke extends TestSuite:
  val tests = Tests:
    test("New C-API"):
      val name: String = "Passthrough"
      // Setup Codes
      // Construct the Arena for Panama linked libraries.
      val arena   = Arena.ofConfined()
      given Arena = arena

      // Load Dialects.
      val context         = summon[ContextApi].contextCreate
      context.loadFirrtlDialect()
      given Context       = context
      val unknownLocation = summon[LocationApi].locationUnknownGet

      // Create MlirModule
      val rootModule: MlirModule = summon[ModuleApi].moduleCreateEmpty(unknownLocation)
      given MlirModule = rootModule

      // Create CirctCircuit
      val circuit: CirctCircuit = org.llvm.circt.scalalib.circuit(name)
      circuit.appendToModule()
      given CirctCircuit = circuit

      // Create CirctModule
      val api = summon[FirrtlBundleFieldApi]
      val typeApi = summon[TypeApi]
      val module: CirctModule = org.llvm.circt.scalalib.module(
        "Passthrough",
        unknownLocation,
          Seq(
            (api.createFirrtlBundleField("i", true, 32.getUInt),unknownLocation),
            (api.createFirrtlBundleField("o", false, 32.getUInt),unknownLocation)
          )
      )
      module.appendToCircuit()

      // Connect i & o
      given CirctModule = module
      org.llvm.circt.scalalib.connect(module.getIO(0), module.getIO(1), unknownLocation)

