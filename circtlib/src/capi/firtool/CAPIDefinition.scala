// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.firtool

import org.llvm.mlir.scalalib.*
import org.llvm.mlir.scalalib.capi.support.{*, given}
import org.llvm.mlir.scalalib.capi.pass.PassManager

import java.lang.foreign.Arena
import java.lang.foreign.MemorySegment

enum CirctFirtoolPreserveAggregateMode:
  case None
  case OneDimVec
  case Vec
  case All
end CirctFirtoolPreserveAggregateMode

trait CirctFirtoolPreserveAggregateModeApi
    extends HasSizeOf[CirctFirtoolPreserveAggregateMode]
    with EnumHasToNative[CirctFirtoolPreserveAggregateMode]

enum CirctFirtoolPreserveValuesMode:
  case Strip
  case None
  case Named
  case All
end CirctFirtoolPreserveValuesMode
trait CirctFirtoolPreserveValuesModeApi
    extends HasSizeOf[CirctFirtoolPreserveValuesMode]
    with EnumHasToNative[CirctFirtoolPreserveValuesMode]

enum CirctFirtoolBuildMode:
  case Default
  case Debug
  case Release
end CirctFirtoolBuildMode
trait CirctFirtoolBuildModeApi extends HasSizeOf[CirctFirtoolBuildMode] with EnumHasToNative[CirctFirtoolBuildMode]

enum CirctFirtoolRandomKind:
  case None
  case Mem
  case Reg
  case All
end CirctFirtoolRandomKind
trait CirctFirtoolRandomKindApi extends HasSizeOf[CirctFirtoolRandomKind] with EnumHasToNative[CirctFirtoolRandomKind]

enum CirctFirtoolCompanionMode:
  case Bind
  case Instantiate
  case Drop
end CirctFirtoolCompanionMode
trait CirctFirtoolCompanionModeApi
    extends HasSizeOf[CirctFirtoolCompanionMode]
    with EnumHasToNative[CirctFirtoolCompanionMode]

enum CirctFirtoolVerificationFlavor:
  case None
  case IfElseFatal
  case Immediate
  case Sva
end CirctFirtoolVerificationFlavor
trait CirctFirtoolVerificationFlavorApi
    extends HasSizeOf[CirctFirtoolVerificationFlavor]
    with EnumHasToNative[CirctFirtoolVerificationFlavor]

class FirtoolOptions(val _segment: MemorySegment)
trait FirtoolOptionsApi extends HasSegment[FirtoolOptions] with HasSizeOf[FirtoolOptions]

trait FirtoolApi:
  inline def firtoolOptionsCreateDefault(
    using arena: Arena
  ): FirtoolOptions
  extension (firtoolOptions: FirtoolOptions)
    inline def destroy(
      using arena: Arena
    ): Unit
    inline def setAddMuxPragmas(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setAddVivadoRAMAddressConflictSynthesisBugWorkaround(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setBlackBoxRootPath(
      value:       String
    )(
      using arena: Arena
    ): Unit
    inline def setBuildMode(
      value:       CirctFirtoolBuildMode
    )(
      using arena: Arena
    ): Unit
    inline def setCkgEnableName(
      value:       String
    )(
      using arena: Arena
    ): Unit
    inline def setCkgInputName(
      value:       String
    )(
      using arena: Arena
    ): Unit
    inline def setCkgModuleName(
      value:       String
    )(
      using arena: Arena
    ): Unit
    inline def setCkgOutputName(
      value:       String
    )(
      using arena: Arena
    ): Unit
    inline def setCkgTestEnableName(
      value:       String
    )(
      using arena: Arena
    ): Unit
    inline def setCompanionMode(
      value:       CirctFirtoolCompanionMode
    )(
      using arena: Arena
    ): Unit
    inline def setDisableAggressiveMergeConnections(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setDisableAnnotationsClassless(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setDisableCSEinClasses(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setDisableLayerSink(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setDisableOptimization(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setDisableRandom(
      value:       CirctFirtoolRandomKind
    )(
      using arena: Arena
    ): Unit
    inline def setDisableUnknownAnnotations(
      disable:     Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setEmitSeparateAlwaysBlocks(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setEnableAnnotationWarning(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setEnableDebugInfo(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setEtcDisableInstanceExtraction(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setEtcDisableModuleInlining(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setEtcDisableRegisterExtraction(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setExportModuleHierarchy(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setExtractTestCode(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setIgnoreReadEnableMem(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setLowerAnnotationsNoRefTypePorts(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setLowerMemories(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setNoDedup(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setOutputAnnotationFilename(
      value:       String
    )(
      using arena: Arena
    ): Unit
    inline def setOutputFilename(
      filename:    String
    )(
      using arena: Arena
    ): Unit
    inline def setPreserveAggregate(
      value:       CirctFirtoolPreserveAggregateMode
    )(
      using arena: Arena
    ): Unit
    inline def setPreserveValues(
      value:       CirctFirtoolPreserveValuesMode
    )(
      using arena: Arena
    ): Unit
    inline def setReplSeqMem(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setReplSeqMemFile(
      value:       String
    )(
      using arena: Arena
    ): Unit
    inline def setSelectDefaultInstanceChoice(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setStripDebugInfo(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setStripFirDebugInfo(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setVbToBv(
      value:       Boolean
    )(
      using arena: Arena
    ): Unit
    inline def setVerificationFlavor(
      value:       CirctFirtoolVerificationFlavor
    )(
      using arena: Arena
    ): Unit
  extension (pm:             PassManager)
    // See inputFilename usage in https://github.com/llvm/circt/blob/ff847edb042541c44c79b59f1a680f641241b485/lib/Firtool/Firtool.cpp#L254
    def chirrtlToLowFIRRTL(
      firtoolOptions: FirtoolOptions
    )(
      using arena:    Arena
    ): LogicalResult
    def exportSplitVerilog(
      firtoolOptions: FirtoolOptions,
      directory:      String
    )(
      using arena:    Arena
    ): LogicalResult
    def exportVerilog(
      firtoolOptions: FirtoolOptions,
      callback:       String => Unit
    )(
      using arena:    Arena
    ): LogicalResult
    def finalizeIR(
      firtoolOptions: FirtoolOptions
    )(
      using arena:    Arena
    ): LogicalResult
    def hwToSV(
      firtoolOptions: FirtoolOptions
    )(
      using arena:    Arena
    ): LogicalResult
    def lowFIRRTLToHW(
      firtoolOptions: FirtoolOptions,
      inputFilename:  String
    )(
      using arena:    Arena
    ): LogicalResult
    def preprocessTransforms(
      firtoolOptions: FirtoolOptions
    )(
      using arena:    Arena
    ): LogicalResult
end FirtoolApi
