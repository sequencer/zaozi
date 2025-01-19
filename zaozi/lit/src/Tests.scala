// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.testutility

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.magic.validateCircuit
import me.jiuyang.zaozi.reftpe.*
import org.llvm.circt.scalalib.firrtl.capi.{
  given_DialectHandleApi,
  given_FirtoolOptionsApi,
  given_ModuleApi,
  given_PassManagerApi,
  FirtoolOptions,
  FirtoolOptionsApi
}
import org.llvm.circt.scalalib.firrtl.operation.{given_CircuitApi, given_ModuleApi, Circuit, CircuitApi}
import org.llvm.mlir.scalalib.{
  given_AttributeApi,
  given_BlockApi,
  given_ContextApi,
  given_IdentifierApi,
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
  NamedAttributeApi,
  OperationApi,
  PassManager,
  Type
}

import java.lang.foreign.Arena

def mlirTest[PARAM <: Parameter, I <: HWInterface[PARAM], P <: DVInterface[PARAM]](
  io:    I,
  probe: P
)(body:  (Arena, Context, Block, Seq[LayerTree]) ?=> (PARAM, Interface[I], Interface[P]) => Unit
)(
  using PARAM
): Unit =
  given Arena      = Arena.ofConfined()
  given Context    = summon[ContextApi].contextCreate
  summon[Context].loadFirrtlDialect()
  given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)

  // Then based on the module to construct the circuit.
  given Circuit = summon[CircuitApi].op(summon[PARAM].moduleName)
  summon[Circuit].appendToModule()
  summon[ConstructorApi].Module(io, probe)(body).appendToCircuit()
  validateCircuit()

  val out = new StringBuilder
  summon[MlirModule].getOperation.print(out ++= _)
  summon[Circuit].operation.print(print)
  summon[Context].destroy()
  summon[Arena].close()

def firrtlTest[PARAM <: Parameter, I <: HWInterface[PARAM], P <: DVInterface[PARAM]](
  io:    I,
  probe: P
)(body:  (Arena, Context, Block, Seq[LayerTree], PARAM, Interface[I], Interface[P]) ?=> Unit
)(
  using PARAM
): Unit =
  given Arena      = Arena.ofConfined()
  given Context    = summon[ContextApi].contextCreate
  summon[Context].loadFirrtlDialect()
  // Then based on the module to construct the circuit.
  given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
  given Circuit    = summon[CircuitApi].op(summon[PARAM].moduleName)
  summon[Circuit].appendToModule()
  summon[ConstructorApi].Module(io, probe)(body).appendToCircuit()

  validateCircuit()
  summon[MlirModule].exportFIRRTL(print)
  summon[Context].destroy()
  summon[Arena].close()

def verilogTest[PARAM <: Parameter, I <: HWInterface[PARAM], P <: DVInterface[PARAM]](
  io:    I,
  probe: P
)(body:  (Arena, Context, Block, Seq[LayerTree], PARAM, Interface[I], Interface[P]) ?=> Unit
)(
  using PARAM
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
  given Circuit    = summon[CircuitApi].op(summon[PARAM].moduleName)
  summon[Circuit].appendToModule()
  summon[ConstructorApi].Module(io, probe)(body).appendToCircuit()
  validateCircuit()
  summon[PassManager].runOnOp(summon[MlirModule].getOperation)
  summon[Context].destroy()
  summon[Arena].close()
