// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.testutility

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import org.llvm.circt.scalalib.firrtl.capi.{
  given_DialectHandleApi,
  given_FirtoolOptionsApi,
  given_ModuleApi,
  FirtoolOptions,
  FirtoolOptionsApi,
  PassManagerApi
}
import org.llvm.circt.scalalib.firrtl.operation.{given_CircuitApi, given_ModuleApi, Circuit, CircuitApi}
import org.llvm.mlir.scalalib.{
  given_ContextApi,
  given_LocationApi,
  given_ModuleApi,
  given_NamedAttributeApi,
  given_OperationApi,
  given_PassManagerApi,
  given_RegionApi,
  given_TypeApi,
  given_ValueApi,
  Block,
  Context,
  ContextApi,
  LocationApi,
  Module as MlirModule,
  ModuleApi as MlirModuleApi,
  PassManager
}
import org.llvm.circt.scalalib.firrtl.capi.given_PassManagerApi
import org.llvm.mlir.scalalib.given_PassManagerApi

import java.lang.foreign.Arena

def mlirTest[P <: Parameter, I <: Interface[P]](
  parameter: P,
  interface: I
)(body:      (Arena, Context, Block) ?=> (P, Wire[I]) => Unit
): Unit =
  given Arena   = Arena.ofConfined()
  given Context = summon[ContextApi].contextCreate
  summon[Context].loadFirrtlDialect()

  // Then based on the module to construct the circuit.
  given Circuit = summon[CircuitApi].op(interface.moduleName)
  summon[ConstructorApi].Module(parameter, interface)(body).appendToCircuit()
  summon[Circuit].operation.print(print)
  summon[Context].destroy()
  summon[Arena].close()

def firrtlTest[P <: Parameter, I <: Interface[P]](
  parameter:  P,
  interface:  I,
  moduleName: Option[String] = None
)(body:       (Arena, Context, Block) ?=> (P, Wire[I]) => Unit
): Unit =
  given Arena      = Arena.ofConfined()
  given Context    = summon[ContextApi].contextCreate
  summon[Context].loadFirrtlDialect()
  // Then based on the module to construct the circuit.
  given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
  given Circuit    = summon[CircuitApi].op(interface.moduleName)
  summon[Circuit].appendToModule()
  summon[ConstructorApi].Module(parameter, interface)(body).appendToCircuit()
  summon[MlirModule].exportFIRRTL(println)
  summon[Context].destroy()
  summon[Arena].close()

def verilogTest[P <: Parameter, I <: Interface[P]](
  parameter:  P,
  interface:  I,
  moduleName: Option[String] = None
)(body:       (Arena, Context, Block) ?=> (P, Wire[I]) => Unit
): Unit =
  given Arena          = Arena.ofConfined()
  given Context        = summon[ContextApi].contextCreate
  summon[Context].loadFirrtlDialect()
  summon[Context].loadSvDialect()
  summon[Context].loadEmitDialect()
  given FirtoolOptions = summon[FirtoolOptionsApi].createDefault()

  given PassManager  = summon[org.llvm.mlir.scalalib.PassManagerApi].passManagerCreate
  val firtoolOptions = summon[FirtoolOptions]
  summon[PassManager].populatePreprocessTransforms(firtoolOptions)
  summon[PassManager].populateCHIRRTLToLowFIRRTL(firtoolOptions, "")
  summon[PassManager].populateLowFIRRTLToHW(firtoolOptions)
  summon[PassManager].populateHWToSV(firtoolOptions)
  // TODO: we need a pass for export verilog on a MLIRModule, not it export empty string.
  summon[PassManager].populateExportVerilog(firtoolOptions, print)

  // Then based on the module to construct the circuit.
  given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
  given Circuit    = summon[CircuitApi].op(interface.moduleName)
  summon[Circuit].appendToModule()
  summon[ConstructorApi].Module(parameter, interface)(body).appendToCircuit()
  summon[PassManager].runOnOp(summon[MlirModule].getOperation)
  summon[Context].destroy()
  summon[Arena].close()
