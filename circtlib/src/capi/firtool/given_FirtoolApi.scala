// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

package org.llvm.circt.scalalib.capi.firtool

import org.llvm.circt.CAPI.{
  circtFirtoolOptionsCreateDefault,
  circtFirtoolOptionsDestroy,
  circtFirtoolOptionsSetAddMuxPragmas,
  circtFirtoolOptionsSetAddVivadoRAMAddressConflictSynthesisBugWorkaround,
  circtFirtoolOptionsSetBlackBoxRootPath,
  circtFirtoolOptionsSetBuildMode,
  circtFirtoolOptionsSetCkgEnableName,
  circtFirtoolOptionsSetCkgInputName,
  circtFirtoolOptionsSetCkgModuleName,
  circtFirtoolOptionsSetCkgOutputName,
  circtFirtoolOptionsSetCkgTestEnableName,
  circtFirtoolOptionsSetCompanionMode,
  circtFirtoolOptionsSetDisableAggressiveMergeConnections,
  circtFirtoolOptionsSetDisableAnnotationsClassless,
  circtFirtoolOptionsSetDisableCSEinClasses,
  circtFirtoolOptionsSetDisableLayerSink,
  circtFirtoolOptionsSetDisableOptimization,
  circtFirtoolOptionsSetDisableRandom,
  circtFirtoolOptionsSetDisableUnknownAnnotations,
  circtFirtoolOptionsSetEmitSeparateAlwaysBlocks,
  circtFirtoolOptionsSetEnableAnnotationWarning,
  circtFirtoolOptionsSetEnableDebugInfo,
  circtFirtoolOptionsSetEtcDisableInstanceExtraction,
  circtFirtoolOptionsSetEtcDisableModuleInlining,
  circtFirtoolOptionsSetEtcDisableRegisterExtraction,
  circtFirtoolOptionsSetExportModuleHierarchy,
  circtFirtoolOptionsSetExtractTestCode,
  circtFirtoolOptionsSetIgnoreReadEnableMem,
  circtFirtoolOptionsSetLowerAnnotationsNoRefTypePorts,
  circtFirtoolOptionsSetLowerMemories,
  circtFirtoolOptionsSetNoDedup,
  circtFirtoolOptionsSetOutputAnnotationFilename,
  circtFirtoolOptionsSetOutputFilename,
  circtFirtoolOptionsSetPreserveAggregate,
  circtFirtoolOptionsSetPreserveValues,
  circtFirtoolOptionsSetReplSeqMem,
  circtFirtoolOptionsSetReplSeqMemFile,
  circtFirtoolOptionsSetSelectDefaultInstanceChoice,
  circtFirtoolOptionsSetStripDebugInfo,
  circtFirtoolOptionsSetStripFirDebugInfo,
  circtFirtoolOptionsSetVbToBv,
  circtFirtoolOptionsSetVerificationFlavor,
  circtFirtoolPopulateCHIRRTLToLowFIRRTL,
  circtFirtoolPopulateExportSplitVerilog,
  circtFirtoolPopulateExportVerilog,
  circtFirtoolPopulateFinalizeIR,
  circtFirtoolPopulateHWToSV,
  circtFirtoolPopulateLowFIRRTLToHW,
  circtFirtoolPopulatePreprocessTransforms
}
import org.llvm.mlir.scalalib.capi.support.{*, given}
import org.llvm.mlir.scalalib.capi.pass.{PassManager, given}

import java.lang.foreign.{Arena, MemorySegment}

given FirtoolApi with
  inline def firtoolOptionsCreateDefault(
    using arena: Arena
  ): FirtoolOptions = FirtoolOptions(circtFirtoolOptionsCreateDefault(arena))
  extension (firtoolOptions: FirtoolOptions)
    inline def destroy(
      using arena: Arena
    ): Unit = circtFirtoolOptionsDestroy(firtoolOptions.segment)
    inline def setAddMuxPragmas(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetAddMuxPragmas(firtoolOptions.segment, value)
    inline def setAddVivadoRAMAddressConflictSynthesisBugWorkaround(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetAddVivadoRAMAddressConflictSynthesisBugWorkaround(firtoolOptions.segment, value)
    inline def setBlackBoxRootPath(
      value:       String
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetBlackBoxRootPath(firtoolOptions.segment, value.toStringRef.segment)
    inline def setBuildMode(
      value:       CirctFirtoolBuildMode
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetBuildMode(firtoolOptions.segment, value.toNative)
    inline def setCkgEnableName(
      value:       String
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetCkgEnableName(firtoolOptions.segment, value.toStringRef.segment)
    inline def setCkgInputName(
      value:       String
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetCkgInputName(firtoolOptions.segment, value.toStringRef.segment)
    inline def setCkgModuleName(
      value:       String
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetCkgModuleName(firtoolOptions.segment, value.toStringRef.segment)
    inline def setCkgOutputName(
      value:       String
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetCkgOutputName(firtoolOptions.segment, value.toStringRef.segment)
    inline def setCkgTestEnableName(
      value:       String
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetCkgTestEnableName(firtoolOptions.segment, value.toStringRef.segment)
    inline def setCompanionMode(
      value:       CirctFirtoolCompanionMode
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetCompanionMode(firtoolOptions.segment, value.toNative)
    inline def setDisableAggressiveMergeConnections(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetDisableAggressiveMergeConnections(firtoolOptions.segment, value)
    inline def setDisableAnnotationsClassless(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetDisableAnnotationsClassless(firtoolOptions.segment, value)
    inline def setDisableCSEinClasses(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetDisableCSEinClasses(firtoolOptions.segment, value)
    inline def setDisableLayerSink(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetDisableLayerSink(firtoolOptions.segment, value)
    inline def setDisableOptimization(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetDisableOptimization(firtoolOptions.segment, value)
    inline def setDisableRandom(
      value:       CirctFirtoolRandomKind
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetDisableRandom(firtoolOptions.segment, value.toNative)
    inline def setDisableUnknownAnnotations(
      disable:     Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetDisableUnknownAnnotations(firtoolOptions.segment, disable)
    inline def setEmitSeparateAlwaysBlocks(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetEmitSeparateAlwaysBlocks(firtoolOptions.segment, value)
    inline def setEnableAnnotationWarning(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetEnableAnnotationWarning(firtoolOptions.segment, value)
    inline def setEnableDebugInfo(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetEnableDebugInfo(firtoolOptions.segment, value)
    inline def setEtcDisableInstanceExtraction(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetEtcDisableInstanceExtraction(firtoolOptions.segment, value)
    inline def setEtcDisableModuleInlining(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetEtcDisableModuleInlining(firtoolOptions.segment, value)
    inline def setEtcDisableRegisterExtraction(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetEtcDisableRegisterExtraction(firtoolOptions.segment, value)
    inline def setExportModuleHierarchy(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetExportModuleHierarchy(firtoolOptions.segment, value)
    inline def setExtractTestCode(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetExtractTestCode(firtoolOptions.segment, value)
    inline def setIgnoreReadEnableMem(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetIgnoreReadEnableMem(firtoolOptions.segment, value)
    inline def setLowerAnnotationsNoRefTypePorts(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetLowerAnnotationsNoRefTypePorts(firtoolOptions.segment, value)
    inline def setLowerMemories(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetLowerMemories(firtoolOptions.segment, value)
    inline def setNoDedup(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetNoDedup(firtoolOptions.segment, value)
    inline def setOutputAnnotationFilename(
      value:       String
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetOutputAnnotationFilename(firtoolOptions.segment, value.toStringRef.segment)
    inline def setOutputFilename(
      filename:    String
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetOutputFilename(firtoolOptions.segment, filename.toStringRef.segment)
    inline def setPreserveAggregate(
      value:       CirctFirtoolPreserveAggregateMode
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetPreserveAggregate(firtoolOptions.segment, value.toNative)
    inline def setPreserveValues(
      value:       CirctFirtoolPreserveValuesMode
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetPreserveValues(firtoolOptions.segment, value.toNative)
    inline def setReplSeqMem(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetReplSeqMem(firtoolOptions.segment, value)
    inline def setReplSeqMemFile(
      value:       String
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetReplSeqMemFile(firtoolOptions.segment, value.toStringRef.segment)
    inline def setSelectDefaultInstanceChoice(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetSelectDefaultInstanceChoice(firtoolOptions.segment, value)
    inline def setStripDebugInfo(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetStripDebugInfo(firtoolOptions.segment, value)
    inline def setStripFirDebugInfo(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetStripFirDebugInfo(firtoolOptions.segment, value)
    inline def setVbToBv(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetVbToBv(firtoolOptions.segment, value)
    inline def setVerificationFlavor(
      value:       CirctFirtoolVerificationFlavor
    )(
      using arena: Arena
    ): Unit = circtFirtoolOptionsSetVerificationFlavor(firtoolOptions.segment, value.toNative)
  extension (pm:             PassManager)
    // See inputFilename usage in https://github.com/llvm/circt/blob/ff847edb042541c44c79b59f1a680f641241b485/lib/Firtool/Firtool.cpp#L254
    def chirrtlToLowFIRRTL(
      firtoolOptions: FirtoolOptions
    )(
      using arena:    Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulateCHIRRTLToLowFIRRTL(
        arena,
        pm.segment,
        firtoolOptions.segment
      )
    )
    def exportSplitVerilog(
      firtoolOptions: FirtoolOptions,
      directory:      String
    )(
      using arena:    Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulateExportSplitVerilog(
        arena,
        pm.segment,
        firtoolOptions.segment,
        directory.toStringRef.segment
      )
    )
    def exportVerilog(
      firtoolOptions: FirtoolOptions,
      callback:       String => Unit
    )(
      using arena:    Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulateExportVerilog(
        arena,
        pm.segment,
        firtoolOptions.segment,
        callback.stringToStringCallback.segment,
        MemorySegment.NULL
      )
    )
    def finalizeIR(
      firtoolOptions: FirtoolOptions
    )(
      using arena:    Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulateFinalizeIR(arena, pm.segment, firtoolOptions.segment)
    )
    def hwToSV(
      firtoolOptions: FirtoolOptions
    )(
      using arena:    Arena
    ): LogicalResult = LogicalResult(circtFirtoolPopulateHWToSV(arena, pm.segment, firtoolOptions.segment))
    def lowFIRRTLToHW(
      firtoolOptions: FirtoolOptions,
      inputFilename:  String
    )(
      using arena:    Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulateLowFIRRTLToHW(
        arena,
        pm.segment,
        firtoolOptions.segment,
        inputFilename.toStringRef.segment
      )
    )
    def preprocessTransforms(
      firtoolOptions: FirtoolOptions
    )(
      using arena:    Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulatePreprocessTransforms(arena, pm.segment, firtoolOptions.segment)
    )
end given
