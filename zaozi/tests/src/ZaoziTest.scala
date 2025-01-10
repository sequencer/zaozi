// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import org.llvm.circt.scalalib.firrtl.capi.{
  given_AttributeApi,
  given_DialectHandleApi,
  given_FirrtlDirectionApi,
  given_FirtoolOptionsApi,
  given_ModuleApi,
  given_PassManagerApi,
  FirrtlConvention,
  FirrtlDirection,
  FirtoolOptions,
  FirtoolOptionsApi,
  PassManagerApi
}
import org.llvm.circt.scalalib.firrtl.operation.{
  given_CircuitApi,
  given_ExtModuleApi,
  given_ModuleApi,
  Circuit,
  CircuitApi,
  ExtModule
}
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
  Type,
  WalkEnum,
  WalkResultEnum
}
import utest.assert

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
  given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)

  // Then based on the module to construct the circuit.
  given Circuit = summon[CircuitApi].op(interface.moduleName)
  summon[Circuit].appendToModule()
  summon[ConstructorApi].Module(parameter, interface)(body).appendToCircuit()
  fixupInstance()

  val out = new StringBuilder
  summon[MlirModule].getOperation.print(out ++= _)
  summon[Context].destroy()
  summon[Arena].close()
  if (checkLines.isEmpty)
    assert(out.toString == "Nothing To Check")
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

  fixupInstance()
  val out = new StringBuilder
  summon[MlirModule].exportFIRRTL(out ++= _)
  summon[Context].destroy()
  summon[Arena].close()
  if (checkLines.isEmpty)
    assert(out.toString == "Nothing To Check")
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
  fixupInstance()
  summon[PassManager].runOnOp(summon[MlirModule].getOperation)
  summon[Context].destroy()
  summon[Arena].close()
  if (checkLines.isEmpty)
    assert(out.toString == "Nothing To Check")
  else checkLines.foreach(l => assert(out.toString.contains(l)))

case class SimpleParameter(width: Int, moduleName: String) extends Parameter

class PassthroughInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter):
  def moduleName: String = parameter.moduleName
  val i = Flipped(UInt(parameter.width.W))
  val o = Aligned(UInt(parameter.width.W))

// Find all instantiated instance and insert to circuit
// TODO: fix duplications
inline def fixupInstance(
)(
  using Arena,
  Context,
  Circuit
): Unit =
  summon[Circuit].block
    .getFirstOperation()
    .walk(
      op =>
        if (op.getName().str() == "firrtl.instance")
          val moduleName: String = op.getInherentAttributeByName("moduleName").flatSymbolRefAttrGetValue
          val name:       String = op.getInherentAttributeByName("name").stringAttrGetValue
          val portDirections = Seq
            .tabulate(op.getNumResults.toInt)(i =>
              op.getInherentAttributeByName("portDirections").denseBoolArrayGetElement(i)
            )
            .map(if (_) FirrtlDirection.Out else FirrtlDirection.In)
            .attrGetPortDirs
          val portNames: Seq[String] = Seq.tabulate(op.getNumResults.toInt)(i =>
            op.getInherentAttributeByName("portNames").arrayAttrGetElement(i).stringAttrGetValue
          )
          val types:     Seq[Type]   = Seq.tabulate(op.getNumResults.toInt)(i => op.getResult(i).getType)
          val extmoduleOp = ExtModule(
            summon[OperationApi].operationCreate(
              name = "firrtl.extmodule",
              location = op.getLocation(),
              namedAttributes =
                val namedAttributeApi = summon[NamedAttributeApi]
                Seq(
                  // ::mlir::StringAttr
                  namedAttributeApi.namedAttributeGet(
                    "sym_name".identifierGet,
                    moduleName.stringAttrGet
                  ),
                  // ::mlir::StringAttr
                  namedAttributeApi.namedAttributeGet(
                    "defname".identifierGet,
                    moduleName.stringAttrGet
                  ),
                  // ::mlir::StringAttr
                  namedAttributeApi.namedAttributeGet(
                    "parameters".identifierGet,
                    Seq.empty.arrayAttrGet
                  ),
                  // ::circt::firrtl::ConventionAttr
                  namedAttributeApi.namedAttributeGet(
                    "convention".identifierGet,
                    FirrtlConvention.Internal.toAttribute
                  ),
                  // ::mlir::DenseBoolArrayAttr
                  namedAttributeApi.namedAttributeGet(
                    "portDirections".identifierGet,
                    portDirections
                  ),
                  // ::mlir::ArrayAttr
                  namedAttributeApi.namedAttributeGet(
                    "portLocations".identifierGet,
                    Seq.fill(op.getNumResults.toInt)(summon[LocationApi].locationUnknownGet.getAttribute).arrayAttrGet
                  ),
                  // ::mlir::ArrayAttr
                  namedAttributeApi.namedAttributeGet(
                    "portAnnotations".identifierGet,
                    Seq.empty.arrayAttrGet
                  ),
                  // ::mlir::ArrayAttr
                  namedAttributeApi.namedAttributeGet(
                    "portSymbols".identifierGet,
                    Seq.empty.arrayAttrGet
                  ),
                  // ::mlir::ArrayAttr
                  namedAttributeApi.namedAttributeGet(
                    "portNames".identifierGet,
                    portNames.map(_.stringAttrGet).arrayAttrGet
                  ),
                  // ::mlir::ArrayAttr
                  namedAttributeApi.namedAttributeGet(
                    "portTypes".identifierGet,
                    types.map(_.typeAttrGet).arrayAttrGet
                  ),
                  // ::mlir::ArrayAttr
                  namedAttributeApi.namedAttributeGet(
                    "annotations".identifierGet,
                    Seq.empty.arrayAttrGet
                  ),
                  // ::mlir::ArrayAttr
                  namedAttributeApi.namedAttributeGet(
                    "layers".identifierGet,
                    Seq.empty.arrayAttrGet
                  ),
                  // ::mlir::ArrayAttr
                  namedAttributeApi.namedAttributeGet(
                    "internalPaths".identifierGet,
                    Seq.empty.arrayAttrGet
                  )
                )
              ,
              regionBlockTypeLocations = Seq(Seq())
            )
          )
          summon[Circuit].block.appendOwnedOperation(extmoduleOp.operation)
        WalkResultEnum.Advance
      ,
      WalkEnum.PreOrder
    )
