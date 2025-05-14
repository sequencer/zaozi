// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.tests

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
import org.llvm.circt.scalalib.emit.capi.given_DialectHandleApi
import org.llvm.circt.scalalib.sv.capi.given_DialectHandleApi
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
import utest.assert

import java.lang.foreign.Arena

trait HasMlirTest:
  this: Generator[?, ?, ?] =>
  private val self = this.asInstanceOf[Generator[this.TPARAM, this.TINTF, this.TPROBE]]

  def mlirTest(
    parameter:  this.TPARAM
  )(checkLines: String*
  ) =
    given Arena      = Arena.ofConfined()
    given Context    = summon[ContextApi].contextCreate
    summon[Context].loadFirrtlDialect()
    given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
    given Circuit    = summon[CircuitApi].op(parameter.moduleName)
    summon[Circuit].appendToModule()
    self.module(parameter).appendToCircuit()
    validateCircuit()

    val out = new StringBuilder
    summon[MlirModule].getOperation.print(out ++= _)
    summon[Context].destroy()
    summon[Arena].close()
    if (checkLines.isEmpty)
      assert(out.toString == "Nothing To Check")
    else checkLines.foreach(l => assert(out.toString.contains(l)))

trait HasFirrtlTest:
  this: Generator[?, ?, ?] =>
  private val self = this.asInstanceOf[Generator[this.TPARAM, this.TINTF, this.TPROBE]]

  def firrtlTest(
    parameter:  this.TPARAM
  )(checkLines: String*
  ) =
    given Arena      = Arena.ofConfined()
    given Context    = summon[ContextApi].contextCreate
    summon[Context].loadFirrtlDialect()
    given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
    given Circuit    = summon[CircuitApi].op(parameter.moduleName)
    summon[Circuit].appendToModule()
    self.module(parameter).appendToCircuit()

    validateCircuit()
    val out = new StringBuilder
    summon[MlirModule].exportFIRRTL(out ++= _)
    summon[Context].destroy()
    summon[Arena].close()
    if (checkLines.isEmpty)
      assert(out.toString == "Nothing To Check")
    else checkLines.foreach(l => assert(out.toString.contains(l)))

trait HasVerilogTest:
  this: Generator[?, ?, ?] =>
  private val self = this.asInstanceOf[Generator[this.TPARAM, this.TINTF, this.TPROBE]]

  def verilogTest(
    parameter:  this.TPARAM
  )(checkLines: String*
  ) =
    given Arena          = Arena.ofConfined()
    given Context        = summon[ContextApi].contextCreate
    summon[Context].loadFirrtlDialect()
    summon[Context].loadSvDialect()
    summon[Context].loadEmitDialect()
    given FirtoolOptions = summon[FirtoolOptionsApi].createDefault()

    given PassManager  = summon[org.llvm.mlir.scalalib.PassManagerApi].passManagerCreate
    val out            = new StringBuilder
    val firtoolOptions = summon[FirtoolOptions]
    summon[PassManager].populatePreprocessTransforms(firtoolOptions)
    summon[PassManager].populateCHIRRTLToLowFIRRTL(firtoolOptions)
    summon[PassManager].populateLowFIRRTLToHW(firtoolOptions, "")
    summon[PassManager].populateHWToSV(firtoolOptions)
    // TODO: we need a pass for export verilog on a MLIRModule, not it export empty string.
    summon[PassManager].populateExportVerilog(firtoolOptions, out ++= _)

    given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
    given Circuit    = summon[CircuitApi].op(parameter.moduleName)
    summon[Circuit].appendToModule()
    self.module(parameter).appendToCircuit()
    validateCircuit()
    summon[PassManager].runOnOp(summon[MlirModule].getOperation)
    summon[Context].destroy()
    summon[Arena].close()
    if (checkLines.isEmpty)
      assert(out.toString == "Nothing To Check")
    else checkLines.foreach(l => assert(out.toString.contains(l)))

trait HasCompileErrorTest:
  this: Generator[?, ?, ?] =>
  private val self = this.asInstanceOf[Generator[this.TPARAM, this.TINTF, this.TPROBE]]

  def compileErrorTest(
    parameter: this.TPARAM
  ) =
    given Arena      = Arena.ofConfined()
    given Context    = summon[ContextApi].contextCreate
    summon[Context].loadFirrtlDialect()
    given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
    given Circuit    = summon[CircuitApi].op(parameter.moduleName)
    summon[Circuit].appendToModule()
    self.module(parameter).appendToCircuit()

    summon[Context].destroy()
    summon[Arena].close()
