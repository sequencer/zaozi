// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.firtoollib
import org.llvm.mlir.scalalib.Context
import org.llvm.circt.scalalib.firrtl.capi.given_FirtoolOptionsApi
import org.llvm.mlir.scalalib.Module as MlirModule
import os.Path
import org.llvm.mlir.scalalib.given_ModuleApi
import org.llvm.mlir.scalalib.ModuleApi as MlirModuleApi

import java.lang.foreign.Arena

given FirtoolOptionsApi with
  extension (firtoolOptions: FirtoolOptions)
    inline def toMlir(
      using Arena,
      Context
    ): org.llvm.circt.scalalib.firrtl.capi.FirtoolOptions =
      val opt = summon[org.llvm.circt.scalalib.firrtl.capi.FirtoolOptionsApi].createDefault()
      opt.setOutputFilename(firtoolOptions.outputFilename)
      opt.setDisableUnknownAnnotations(firtoolOptions.disableUnknownAnnotations)
      opt.setDisableAnnotationsClassless(firtoolOptions.disableAnnotationsClassless)
      opt.setLowerAnnotationsNoRefTypePorts(firtoolOptions.lowerAnnotationsNoRefTypePorts)
      opt.setAllowAddingPortsOnPublic(firtoolOptions.allowAddingPortsOnPublic)
      opt.setPreserveAggregate(firtoolOptions.preserveAggregate match {
        case PreserveAggregateMode.None      =>
          org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolPreserveAggregateMode.None
        case PreserveAggregateMode.OneDimVec =>
          org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolPreserveAggregateMode.OneDimVec
        case PreserveAggregateMode.Vec       =>
          org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolPreserveAggregateMode.Vec
        case PreserveAggregateMode.All       =>
          org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolPreserveAggregateMode.All
      })
      opt.setPreserveValues(firtoolOptions.preserveValues match {
        case PreserveValuesMode.Strip =>
          org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolPreserveValuesMode.Strip
        case PreserveValuesMode.None  =>
          org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolPreserveValuesMode.None
        case PreserveValuesMode.Named =>
          org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolPreserveValuesMode.Named
        case PreserveValuesMode.All   => org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolPreserveValuesMode.All
      })
      opt.setEnableDebugInfo(firtoolOptions.enableDebugInfo)
      opt.setBuildMode(firtoolOptions.buildMode match {
        case BuildMode.Default => org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolBuildMode.Default
        case BuildMode.Debug   => org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolBuildMode.Debug
        case BuildMode.Release => org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolBuildMode.Release
      })
      opt.setDisableLayerSink(firtoolOptions.disableLayerSink)
      opt.setDisableOptimization(firtoolOptions.disableOptimization)
      opt.setExportChiselInterface(firtoolOptions.exportChiselInterface)
      opt.setChiselInterfaceOutDirectory(firtoolOptions.chiselInterfaceOutDirectory)
      opt.setVbToBv(firtoolOptions.vbToBv)
      opt.setNoDedup(firtoolOptions.noDedup)
      opt.setCompanionMode(firtoolOptions.companionMode match {
        case CompanionMode.Bind        => org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolCompanionMode.Bind
        case CompanionMode.Instantiate =>
          org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolCompanionMode.Instantiate
        case CompanionMode.Drop        => org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolCompanionMode.Drop
      })
      opt.setDisableAggressiveMergeConnections(firtoolOptions.disableAggressiveMergeConnections)
      opt.setLowerMemories(firtoolOptions.lowerMemories)
      opt.setBlackBoxRootPath(firtoolOptions.blackBoxRootPath)
      opt.setReplSeqMem(firtoolOptions.replSeqMem)
      opt.setReplSeqMemFile(firtoolOptions.replSeqMemFile)
      opt.setExtractTestCode(firtoolOptions.extractTestCode)
      opt.setIgnoreReadEnableMem(firtoolOptions.ignoreReadEnableMem)
      opt.setDisableRandom(firtoolOptions.disableRandom match {
        case RandomKind.None => org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolRandomKind.None
        case RandomKind.Mem  => org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolRandomKind.Mem
        case RandomKind.Reg  => org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolRandomKind.Reg
        case RandomKind.All  => org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolRandomKind.All
      })
      opt.setOutputAnnotationFilename(firtoolOptions.outputAnnotationFilename)
      opt.setEnableAnnotationWarning(firtoolOptions.enableAnnotationWarning)
      opt.setAddMuxPragmas(firtoolOptions.addMuxPragmas)
      opt.setVerificationFlavor(firtoolOptions.verificationFlavor match {
        case VerificationFlavor.None        =>
          org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolVerificationFlavor.None
        case VerificationFlavor.IfElseFatal =>
          org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolVerificationFlavor.IfElseFatal
        case VerificationFlavor.Immediate   =>
          org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolVerificationFlavor.Immediate
        case VerificationFlavor.Sva         => org.llvm.circt.scalalib.firrtl.capi.CirctFirtoolVerificationFlavor.Sva
      })
      opt.setEmitSeparateAlwaysBlocks(firtoolOptions.emitSeparateAlwaysBlocks)
      opt.setEtcDisableInstanceExtraction(firtoolOptions.etcDisableInstanceExtraction)
      opt.setEtcDisableRegisterExtraction(firtoolOptions.etcDisableRegisterExtraction)
      opt.setEtcDisableModuleInlining(firtoolOptions.etcDisableModuleInlining)
      opt.setAddVivadoRAMAddressConflictSynthesisBugWorkaround(
        firtoolOptions.addVivadoRAMAddressConflictSynthesisBugWorkaround
      )
      opt.setCkgModuleName(firtoolOptions.ckgModuleName)
      opt.setCkgInputName(firtoolOptions.ckgInputName)
      opt.setCkgOutputName(firtoolOptions.ckgOutputName)
      opt.setCkgEnableName(firtoolOptions.ckgEnableName)
      opt.setCkgTestEnableName(firtoolOptions.ckgTestEnableName)
      opt.setExportModuleHierarchy(firtoolOptions.exportModuleHierarchy)
      opt.setStripFirDebugInfo(firtoolOptions.stripFirDebugInfo)
      opt.setStripDebugInfo(firtoolOptions.stripDebugInfo)
      opt.setDisableCSEinClasses(firtoolOptions.disableCSEinClasses)
      opt.setSelectDefaultInstanceChoice(firtoolOptions.selectDefaultInstanceChoice)
      opt
end given

given FirtoolApi with
  def parseMlir(
    path: Path
  )(
    using Arena,
    Context
  ): MlirModule =
    if (path.ext == "mlir")
      summon[MlirModuleApi].moduleCreateParse(os.read(path))
    else if (path.ext == "mlirbc")
      summon[MlirModuleApi].moduleCreateParse(os.read.bytes(path))
    else
      throw new Exception("not a valid mlir file")
  def importFirrtl(
    path: Path
  )(
    using Arena,
    Context
  ): MlirModule = ???

  def importVerilog(
    paths: Seq[Path]
  )(
    using Arena,
    Context
  ): MlirModule = ???

  def getInstanceGraph(
    mlirModule: MlirModule
  )(
    using Arena,
    Context
  ): InstanceGraph = ???

  def getPortList(
    mlirModule: MlirModule,
    moduleName: String
  )(
    using Arena,
    Context
  ): Seq[Port] = ???
end given
