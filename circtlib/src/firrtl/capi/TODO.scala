// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.firrtl.capi

import org.llvm.circt.*
import org.llvm.circt.CAPI.{mlirGetDialectHandle__firrtl__ as mlirGetDialectHandle, *}
import org.llvm.mlir.scalalib.{
  given_AttributeApi,
  Attribute,
  Context,
  DialectHandle,
  Identifier,
  LogicalResult,
  Module,
  PassManager,
  Type,
  Value,
  given
}

import java.lang.foreign.{Arena, MemorySegment}

given FirtoolOptionsApi with
  inline def createDefault(
  )(
    using arena: Arena
  ): FirtoolOptions = FirtoolOptions(circtFirtoolOptionsCreateDefault(arena))
  extension (firtoolOptions: FirtoolOptions)
    inline def destroy(
    )(
      using Arena
    ): Unit = circtFirtoolOptionsDestroy(firtoolOptions.segment)
    inline def setOutputFilename(
      filename: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetOutputFilename(firtoolOptions.segment, filename.toStringRef.segment)
    inline def setDisableUnknownAnnotations(
      disable: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetDisableUnknownAnnotations(firtoolOptions.segment, disable)
    inline def setDisableAnnotationsClassless(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetDisableAnnotationsClassless(firtoolOptions.segment, value)
    inline def setLowerAnnotationsNoRefTypePorts(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetLowerAnnotationsNoRefTypePorts(firtoolOptions.segment, value)
    inline def setAllowAddingPortsOnPublic(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetAllowAddingPortsOnPublic(firtoolOptions.segment, value)
    inline def setPreserveAggregate(
      value: CirctFirtoolPreserveAggregateMode
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetPreserveAggregate(firtoolOptions.segment, value.toNative)
    inline def setPreserveValues(
      value: CirctFirtoolPreserveValuesMode
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetPreserveValues(firtoolOptions.segment, value.toNative)
    inline def setEnableDebugInfo(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetEnableDebugInfo(firtoolOptions.segment, value)
    inline def setBuildMode(
      value: CirctFirtoolBuildMode
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetBuildMode(firtoolOptions.segment, value.toNative)
    inline def setDisableLayerSink(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetDisableLayerSink(firtoolOptions.segment, value)
    inline def setDisableOptimization(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetDisableOptimization(firtoolOptions.segment, value)
    inline def setExportChiselInterface(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetExportChiselInterface(firtoolOptions.segment, value)
    inline def setChiselInterfaceOutDirectory(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetChiselInterfaceOutDirectory(firtoolOptions.segment, value.toStringRef.segment)
    inline def setVbToBv(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetVbToBv(firtoolOptions.segment, value)
    inline def setNoDedup(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetNoDedup(firtoolOptions.segment, value)
    inline def setCompanionMode(
      value: CirctFirtoolCompanionMode
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetCompanionMode(firtoolOptions.segment, value.toNative)
    inline def setDisableAggressiveMergeConnections(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetDisableAggressiveMergeConnections(firtoolOptions.segment, value)
    inline def setLowerMemories(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetLowerMemories(firtoolOptions.segment, value)
    inline def setBlackBoxRootPath(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetBlackBoxRootPath(firtoolOptions.segment, value.toStringRef.segment)
    inline def setReplSeqMem(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetReplSeqMem(firtoolOptions.segment, value)
    inline def setReplSeqMemFile(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetReplSeqMemFile(firtoolOptions.segment, value.toStringRef.segment)
    inline def setExtractTestCode(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetExtractTestCode(firtoolOptions.segment, value)
    inline def setIgnoreReadEnableMem(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetIgnoreReadEnableMem(firtoolOptions.segment, value)
    inline def setDisableRandom(
      value: CirctFirtoolRandomKind
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetDisableRandom(firtoolOptions.segment, value.toNative)
    inline def setOutputAnnotationFilename(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetOutputAnnotationFilename(firtoolOptions.segment, value.toStringRef.segment)
    inline def setEnableAnnotationWarning(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetEnableAnnotationWarning(firtoolOptions.segment, value)
    inline def setAddMuxPragmas(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetAddMuxPragmas(firtoolOptions.segment, value)
    inline def setVerificationFlavor(
      value: CirctFirtoolVerificationFlavor
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetVerificationFlavor(firtoolOptions.segment, value.toNative)
    inline def setEmitSeparateAlwaysBlocks(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetEmitSeparateAlwaysBlocks(firtoolOptions.segment, value)
    inline def setEtcDisableInstanceExtraction(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetEtcDisableInstanceExtraction(firtoolOptions.segment, value)
    inline def setEtcDisableRegisterExtraction(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetEtcDisableRegisterExtraction(firtoolOptions.segment, value)
    inline def setEtcDisableModuleInlining(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetEtcDisableModuleInlining(firtoolOptions.segment, value)
    inline def setAddVivadoRAMAddressConflictSynthesisBugWorkaround(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetAddVivadoRAMAddressConflictSynthesisBugWorkaround(firtoolOptions.segment, value)
    inline def setCkgModuleName(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetCkgModuleName(firtoolOptions.segment, value.toStringRef.segment)
    inline def setCkgInputName(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetCkgInputName(firtoolOptions.segment, value.toStringRef.segment)
    inline def setCkgOutputName(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetCkgOutputName(firtoolOptions.segment, value.toStringRef.segment)
    inline def setCkgEnableName(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetCkgEnableName(firtoolOptions.segment, value.toStringRef.segment)
    inline def setCkgTestEnableName(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetCkgTestEnableName(firtoolOptions.segment, value.toStringRef.segment)
    inline def setExportModuleHierarchy(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetExportModuleHierarchy(firtoolOptions.segment, value)
    inline def setStripFirDebugInfo(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetStripFirDebugInfo(firtoolOptions.segment, value)
    inline def setStripDebugInfo(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetStripDebugInfo(firtoolOptions.segment, value)
    inline def setDisableCSEinClasses(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetDisableCSEinClasses(firtoolOptions.segment, value)
    inline def setSelectDefaultInstanceChoice(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetSelectDefaultInstanceChoice(firtoolOptions.segment, value)

    inline def segment: MemorySegment = firtoolOptions._segment
    inline def sizeOf:  Int           = CirctFirtoolFirtoolOptions.sizeof().toInt
end given

given PassManagerApi with
  extension (pm: PassManager)
    def populatePreprocessTransforms(
      firtoolOptions: FirtoolOptions
    )(
      using Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulatePreprocessTransforms(summon[Arena], pm.segment, firtoolOptions.segment)
    )
    // See inputFilename usage in https://github.com/llvm/circt/blob/ff847edb042541c44c79b59f1a680f641241b485/lib/Firtool/Firtool.cpp#L254
    def populateCHIRRTLToLowFIRRTL(
      firtoolOptions: FirtoolOptions
    )(
      using Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulateCHIRRTLToLowFIRRTL(
        summon[Arena],
        pm.segment,
        firtoolOptions.segment
      )
    )
    def populateLowFIRRTLToHW(
      firtoolOptions: FirtoolOptions,
      inputFilename:  String
    )(
      using Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulateLowFIRRTLToHW(
        summon[Arena],
        pm.segment,
        firtoolOptions.segment,
        inputFilename.toStringRef.segment
      )
    )
    def populateHWToSV(
      firtoolOptions: FirtoolOptions
    )(
      using Arena
    ): LogicalResult = LogicalResult(circtFirtoolPopulateHWToSV(summon[Arena], pm.segment, firtoolOptions.segment))
    def populateExportVerilog(
      firtoolOptions: FirtoolOptions,
      callback:       String => Unit
    )(
      using Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulateExportVerilog(
        summon[Arena],
        pm.segment,
        firtoolOptions.segment,
        callback.stringToStringCallback.segment,
        MemorySegment.NULL
      )
    )
    def populateExportSplitVerilog(
      firtoolOptions: FirtoolOptions,
      directory:      String
    )(
      using Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulateExportSplitVerilog(
        summon[Arena],
        pm.segment,
        firtoolOptions.segment,
        directory.toStringRef.segment
      )
    )
    def populateFinalizeIR(
      firtoolOptions: FirtoolOptions
    )(
      using Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulateFinalizeIR(summon[Arena], pm.segment, firtoolOptions.segment)
    )
end given

given ModuleApi with
  extension (module: Module)
    inline def exportFIRRTL(
      callback:    String => Unit
    )(
      using arena: Arena
    ): Unit =
      LogicalResult(
        mlirExportFIRRTL(arena, module.segment, callback.stringToStringCallback.segment, MemorySegment.NULL)
      )
    inline def exportVerilog(
      callback:    String => Unit
    )(
      using arena: Arena
    ): LogicalResult =
      LogicalResult(
        mlirExportVerilog(arena, module.segment, callback.stringToStringCallback.segment, MemorySegment.NULL)
      )
    inline def exportSplitVerilog(
      directory:   String
    )(
      using arena: Arena
    ): LogicalResult =
      LogicalResult(mlirExportSplitVerilog(arena, module.segment, directory.toStringRef.segment))
end given
