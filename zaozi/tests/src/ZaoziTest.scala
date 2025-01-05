// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import org.llvm.circt.scalalib.firrtl.capi.{FirtoolOptions, FirtoolOptionsApi, PassManagerApi, given_DialectHandleApi, given_FirtoolOptionsApi, given_ModuleApi}
import org.llvm.circt.scalalib.firrtl.operation.{Circuit, CircuitApi, given_CircuitApi, given_ModuleApi}
import org.llvm.mlir.scalalib.{Block, Context, ContextApi, LocationApi, PassManager, given_PassManagerApi, given_ContextApi, given_LocationApi, given_ModuleApi, given_NamedAttributeApi, given_OperationApi, given_RegionApi, given_TypeApi, given_ValueApi, Module as MlirModule, ModuleApi as MlirModuleApi}
import org.llvm.circt.scalalib.firrtl.capi.given_PassManagerApi
import org.llvm.mlir.scalalib.given_PassManagerApi

import java.lang.foreign.Arena

def mlirTest[P <: Parameter, I <: Interface[P]](
  parameter:  P,
  interface:  I,
)(checkLines: String*
)(body:       (Arena, Context, Block) ?=> (P, Wire[I]) => Unit
): Unit =
  given Arena = Arena.ofConfined()
  given Context = summon[ContextApi].contextCreate
  summon[Context].loadFirrtlDialect()

  // Then based on the module to construct the circuit.
  given Circuit = summon[CircuitApi].op(interface.moduleName)
  summon[ConstructorApi].Module(parameter, interface)(body).appendToCircuit()

  val out = new StringBuilder
  summon[Circuit].operation.print(out ++= _)
  summon[Context].destroy()
  summon[Arena].close()
  if (checkLines.isEmpty)
    println(s"please add lines to check for:\n$out")
    assert(false)
  else checkLines.foreach(l => assert(out.toString.contains(l)))


def firrtlTest[P <: Parameter, I <: Interface[P]](
  parameter:  P,
  interface:  I,
  moduleName: Option[String] = None
)(checkLines: String*
)(body:       (Arena, Context, Block) ?=> (P, Wire[I]) => Unit
): Unit =
  given Arena = Arena.ofConfined()
  given Context = summon[ContextApi].contextCreate
  summon[Context].loadFirrtlDialect()
  // Then based on the module to construct the circuit.
  given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
  given Circuit    = summon[CircuitApi].op(interface.moduleName)
  summon[Circuit].appendToModule()
  summon[ConstructorApi].Module(parameter, interface)(body).appendToCircuit()

  val out = new StringBuilder
  summon[MlirModule].exportFIRRTL(out ++= _)
  summon[Context].destroy()
  summon[Arena].close()
  if (checkLines.isEmpty)
    println(s"please add lines to check for:\n$out")
    assert(false)
  else checkLines.foreach(l => assert(out.toString.contains(l)))

def verilogTest[P <: Parameter, I <: Interface[P]](
  parameter:  P,
  interface:  I,
  moduleName: Option[String] = None
)(checkLines: String*
)(body:       (Arena, Context, Block) ?=> (P, Wire[I]) => Unit
): Unit =
  given Arena = Arena.ofConfined()
  given Context = summon[ContextApi].contextCreate
  summon[Context].loadFirrtlDialect()
  summon[Context].loadSvDialect()
  summon[Context].loadEmitDialect()
  given FirtoolOptions = summon[FirtoolOptionsApi].createDefault()

  given PassManager = summon[org.llvm.mlir.scalalib.PassManagerApi].passManagerCreate
  val out = new StringBuilder
  val firtoolOptions = summon[FirtoolOptions]
  summon[PassManager].populatePreprocessTransforms(firtoolOptions)
  summon[PassManager].populateCHIRRTLToLowFIRRTL(firtoolOptions, "")
  summon[PassManager].populateLowFIRRTLToHW(firtoolOptions)
  summon[PassManager].populateHWToSV(firtoolOptions)
  // TODO: we need a pass for export verilog on a MLIRModule, not it export empty string.
  summon[PassManager].populateExportVerilog(firtoolOptions, out ++= _)

  // Then based on the module to construct the circuit.
  given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
  given Circuit    = summon[CircuitApi].op(interface.moduleName)
  summon[Circuit].appendToModule()
  summon[ConstructorApi].Module(parameter, interface)(body).appendToCircuit()
  summon[PassManager].runOnOp(summon[MlirModule].getOperation)
  summon[Context].destroy()
  summon[Arena].close()
  if (checkLines.isEmpty)
    println(s"please add lines to check for:\n${out.toString}")
    assert(false)
  else checkLines.foreach(l => assert(out.toString.contains(l)))

case class SimpleParameter(width: Int, moduleName: String) extends Parameter

class PassthroughInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter):
  def moduleName: String = parameter.moduleName
  val i = Flipped(UInt(parameter.width.W))
  val o = Aligned(UInt(parameter.width.W))
