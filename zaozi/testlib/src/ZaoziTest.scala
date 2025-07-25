// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.testlib

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.magic.validateCircuit
import me.jiuyang.zaozi.reftpe.*
import org.llvm.circt.scalalib.capi.dialect.firrtl.DialectApi as FirrtlDialectApi
import org.llvm.circt.scalalib.capi.dialect.sv.DialectApi as SvDialectApi
import org.llvm.circt.scalalib.capi.dialect.emit.DialectApi as EmitDialectApi
import org.llvm.circt.scalalib.capi.dialect.firrtl.given_DialectApi
import org.llvm.circt.scalalib.capi.firtool.given_FirtoolOptionsApi
import org.llvm.circt.scalalib.dialect.firrtl.operation.{given_CircuitApi, given_ModuleApi, Circuit, CircuitApi}
import org.llvm.circt.scalalib.capi.dialect.emit.given_DialectApi
import org.llvm.circt.scalalib.capi.dialect.sv.given_DialectApi
import org.llvm.circt.scalalib.capi.firtool.FirtoolApi
import org.llvm.circt.scalalib.capi.firtool.given
import org.llvm.circt.scalalib.capi.firtool.FirtoolOptions
import org.llvm.circt.scalalib.capi.exportfirrtl.given_ExportFirrtlApi
import org.llvm.mlir.scalalib.capi.ir.{
  given_AttributeApi,
  given_BlockApi,
  given_ContextApi,
  given_IdentifierApi,
  given_LocationApi,
  given_ModuleApi,
  given_NamedAttributeApi,
  given_OperationApi,
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
  Type
}
import org.llvm.mlir.scalalib.capi.pass.{given_PassManagerApi, PassManager, PassManagerApi}
import utest.assert

import java.lang.foreign.Arena

trait HasMlirTest:
  this: Generator[?, ?, ?, ?] =>
  private val self = this.asInstanceOf[Generator[this.TPARAM, this.TLAYER, this.TINTF, this.TPROBE]]

  def mlirTest(
    parameter: this.TPARAM
  )(predicate: String => Boolean
  ): Unit =
    given Arena      = Arena.ofConfined()
    given Context    = summon[ContextApi].contextCreate
    summon[FirrtlDialectApi].loadDialect
    given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
    given Circuit    = summon[CircuitApi].op(self.moduleName(parameter))
    summon[Circuit].appendToModule()
    self.module(parameter).appendToCircuit()
    validateCircuit()

    val out = new StringBuilder
    summon[MlirModule].getOperation.print(out ++= _)
    summon[Context].destroy()
    summon[Arena].close()

    assert(predicate(out.toString))

  def mlirTest(
    parameter:  this.TPARAM
  )(checkLines: String*
  ): Unit = mlirTest(parameter)(out => checkLines.forall(l => out.contains(l)))

trait HasFirrtlTest:
  this: Generator[?, ?, ?, ?] =>
  private val self = this.asInstanceOf[Generator[this.TPARAM, this.TLAYER, this.TINTF, this.TPROBE]]

  def firrtlTest(
    parameter: this.TPARAM
  )(predicate: String => Boolean
  ): Unit =
    given Arena      = Arena.ofConfined()
    given Context    = summon[ContextApi].contextCreate
    summon[FirrtlDialectApi].loadDialect
    given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
    given Circuit    = summon[CircuitApi].op(self.moduleName(parameter))
    summon[Circuit].appendToModule()
    self.module(parameter).appendToCircuit()

    validateCircuit()
    val out = new StringBuilder
    summon[MlirModule].exportFIRRTL(out ++= _)
    summon[Context].destroy()
    summon[Arena].close()

    assert(predicate(out.toString))

  def firrtlTest(
    parameter:  this.TPARAM
  )(checkLines: String*
  ): Unit = firrtlTest(parameter)(out => checkLines.forall(l => out.contains(l)))

trait HasVerilogTest:
  this: Generator[?, ?, ?, ?] =>
  private val self = this.asInstanceOf[Generator[this.TPARAM, this.TLAYER, this.TINTF, this.TPROBE]]

  def verilogTest(
    parameter: this.TPARAM
  )(predicate: String => Boolean
  ): Unit =
    given Arena          = Arena.ofConfined()
    given Context        = summon[ContextApi].contextCreate
    summon[FirrtlDialectApi].loadDialect
    summon[SvDialectApi].loadDialect
    summon[EmitDialectApi].loadDialect
    given FirtoolOptions = summon[FirtoolApi].firtoolOptionsCreateDefault

    given PassManager  = summon[PassManagerApi].passManagerCreate
    val out            = new StringBuilder
    val firtoolOptions = summon[FirtoolOptions]

    summon[PassManager].preprocessTransforms(firtoolOptions)
    summon[PassManager].chirrtlToLowFIRRTL(firtoolOptions)
    summon[PassManager].lowFIRRTLToHW(firtoolOptions, "")
    summon[PassManager].hwToSV(firtoolOptions)
    // TODO: we need a pass for export verilog on a MLIRModule, not it export empty string.
    summon[PassManager].exportVerilog(firtoolOptions, out ++= _)

    given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
    given Circuit    = summon[CircuitApi].op(self.moduleName(parameter))
    summon[Circuit].appendToModule()
    self.module(parameter).appendToCircuit()
    validateCircuit()
    summon[PassManager].runOnOp(summon[MlirModule].getOperation)
    summon[Context].destroy()
    summon[Arena].close()

    assert(predicate(out.toString))

  def verilogTest(
    parameter:  this.TPARAM
  )(checkLines: String*
  ): Unit = verilogTest(parameter)(out => checkLines.forall(l => out.contains(l)))

trait HasCompileErrorTest:
  this: Generator[?, ?, ?, ?] =>
  private val self = this.asInstanceOf[Generator[this.TPARAM, this.TLAYER, this.TINTF, this.TPROBE]]

  def compileErrorTest(
    parameter: this.TPARAM
  ) =
    given Arena      = Arena.ofConfined()
    given Context    = summon[ContextApi].contextCreate
    summon[FirrtlDialectApi].loadDialect
    given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
    given Circuit    = summon[CircuitApi].op(self.moduleName(parameter))
    summon[Circuit].appendToModule()
    self.module(parameter).appendToCircuit()

    summon[Context].destroy()
    summon[Arena].close()
