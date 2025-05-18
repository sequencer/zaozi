// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.firtoollib
import org.llvm.mlir.scalalib.Context

import java.lang.foreign.Arena

enum PreserveAggregateMode:
  case None
  case OneDimVec
  case Vec
  case All
end PreserveAggregateMode

enum PreserveValuesMode:
  case Strip
  case None
  case Named
  case All
end PreserveValuesMode

enum BuildMode:
  case Default
  case Debug
  case Release
end BuildMode

enum CompanionMode:
  case Bind
  case Instantiate
  case Drop
end CompanionMode

enum RandomKind:
  case None
  case Mem
  case Reg
  case All
end RandomKind

enum VerificationFlavor:
  case None
  case IfElseFatal
  case Immediate
  case Sva
end VerificationFlavor

case class FirtoolOptions(
  outputFilename:                                    String,
  disableUnknownAnnotations:                         Boolean,
  disableAnnotationsClassless:                       Boolean,
  lowerAnnotationsNoRefTypePorts:                    Boolean,
  allowAddingPortsOnPublic:                          Boolean,
  preserveAggregate:                                 PreserveAggregateMode,
  preserveValues:                                    PreserveValuesMode,
  enableDebugInfo:                                   Boolean,
  buildMode:                                         BuildMode,
  disableLayerSink:                                  Boolean,
  disableOptimization:                               Boolean,
  exportChiselInterface:                             Boolean,
  chiselInterfaceOutDirectory:                       String,
  vbToBv:                                            Boolean,
  noDedup:                                           Boolean,
  companionMode:                                     CompanionMode,
  disableAggressiveMergeConnections:                 Boolean,
  lowerMemories:                                     Boolean,
  blackBoxRootPath:                                  String,
  replSeqMem:                                        Boolean,
  replSeqMemFile:                                    String,
  extractTestCode:                                   Boolean,
  ignoreReadEnableMem:                               Boolean,
  disableRandom:                                     RandomKind,
  outputAnnotationFilename:                          String,
  enableAnnotationWarning:                           Boolean,
  addMuxPragmas:                                     Boolean,
  verificationFlavor:                                VerificationFlavor,
  emitSeparateAlwaysBlocks:                          Boolean,
  etcDisableInstanceExtraction:                      Boolean,
  etcDisableRegisterExtraction:                      Boolean,
  etcDisableModuleInlining:                          Boolean,
  addVivadoRAMAddressConflictSynthesisBugWorkaround: Boolean,
  ckgModuleName:                                     String,
  ckgInputName:                                      String,
  ckgOutputName:                                     String,
  ckgEnableName:                                     String,
  ckgTestEnableName:                                 String,
  exportModuleHierarchy:                             Boolean,
  stripFirDebugInfo:                                 Boolean,
  stripDebugInfo:                                    Boolean,
  disableCSEinClasses:                               Boolean,
  selectDefaultInstanceChoice:                       Boolean)

trait FirtoolOptionsApi:
  extension (firtoolOptions: FirtoolOptions)
    inline def toMlir(
      using Arena,
      Context
    ): org.llvm.circt.scalalib.firrtl.capi.FirtoolOptions
end FirtoolOptionsApi
