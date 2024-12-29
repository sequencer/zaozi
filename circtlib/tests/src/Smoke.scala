// SPDX-License-Identifier: Apache-2.0
package me.jiuyang.zaozi.circtlib.tests

import org.llvm.circt.scalalib.operator.Circuit
import org.llvm.circt.scalalib.{*, given}
import org.llvm.mlir.scalalib.{Context, ContextApi, LocationApi, ModuleApi, Module as MlirModule, given}
import utest.*

import java.lang.foreign.Arena

object Smoke extends TestSuite:
  val tests = Tests:
    test("Passthrough"):
      val name: String = "Passthrough"
      // Setup Codes
      // Construct the Arena for Panama linked libraries.
      val arena = Arena.ofConfined()

      given Arena = arena

      // Load Dialects.
      val context = summon[ContextApi].contextCreate
      context.loadFirrtlDialect()

      given Context = context

      val unknownLocation = summon[LocationApi].locationUnknownGet

      // Create MlirModule
      val rootModule: MlirModule = summon[ModuleApi].moduleCreateEmpty(unknownLocation)

      given MlirModule = rootModule

      // Create CirctCircuit
      val circuit: Circuit = operator.circuit(name)
      circuit.appendToModule()

      given Circuit = circuit

      // Create CirctModule
      val api = summon[FirrtlBundleFieldApi]
      val typeApi = summon[TypeApi]
      val module: operator.Module = operator.module(
        "Passthrough",
        unknownLocation,
        Seq(
          (api.createFirrtlBundleField("i", true, 32.getUInt), unknownLocation),
          (api.createFirrtlBundleField("o", false, 32.getUInt), unknownLocation)
        )
      )
      module.appendToCircuit()

      // Connect i & o
      given operator.Module = module

      operator.connect(module.getIO(0), module.getIO(1), unknownLocation)
      summon[org.llvm.circt.scalalib.ModuleApi]
      val out = new StringBuilder
      rootModule.exportFIRRTL(out ++= _)
      assert(out.toString.contains(
        """circuit Passthrough :
          |  public module Passthrough :
          |    input i : UInt<32>
          |    output o : UInt<32>
          |
          |    connect o, i
          |""".stripMargin))
