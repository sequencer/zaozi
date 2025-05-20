// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.conversion

import org.llvm.circt.CAPI.{
  mlirCreateCIRCTConversionAffineToLoopSchedule,
  mlirCreateCIRCTConversionCFToHandshake,
  mlirCreateCIRCTConversionCalyxNative,
  mlirCreateCIRCTConversionCalyxRemoveGroupsFromFSM,
  mlirCreateCIRCTConversionCalyxToFSM,
  mlirCreateCIRCTConversionCalyxToHW,
  mlirCreateCIRCTConversionConvertAIGToComb,
  mlirCreateCIRCTConversionConvertCombToAIG,
  mlirCreateCIRCTConversionConvertCombToArith,
  mlirCreateCIRCTConversionConvertCombToSMT,
  mlirCreateCIRCTConversionConvertFSMToSV,
  mlirCreateCIRCTConversionConvertHWToBTOR2,
  mlirCreateCIRCTConversionConvertHWToLLVM,
  mlirCreateCIRCTConversionConvertHWToSMT,
  mlirCreateCIRCTConversionConvertHWToSystemC,
  mlirCreateCIRCTConversionConvertMooreToCore,
  mlirCreateCIRCTConversionConvertToArcs,
  mlirCreateCIRCTConversionConvertVerifToSMT,
  mlirCreateCIRCTConversionDCToHW,
  mlirCreateCIRCTConversionExportChiselInterface,
  mlirCreateCIRCTConversionExportSplitChiselInterface,
  mlirCreateCIRCTConversionExportSplitVerilog,
  mlirCreateCIRCTConversionExportVerilog,
  mlirCreateCIRCTConversionHWArithToHW,
  mlirCreateCIRCTConversionHWLowerInstanceChoices,
  mlirCreateCIRCTConversionHandshakeRemoveBlock,
  mlirCreateCIRCTConversionHandshakeToDC,
  mlirCreateCIRCTConversionHandshakeToHW,
  mlirCreateCIRCTConversionLegalizeAnonEnums,
  mlirCreateCIRCTConversionLoopScheduleToCalyx,
  mlirCreateCIRCTConversionLowerArcToLLVM,
  mlirCreateCIRCTConversionLowerFIRRTLToHW,
  mlirCreateCIRCTConversionLowerFirMem,
  mlirCreateCIRCTConversionLowerHWToSV,
  mlirCreateCIRCTConversionLowerLTLToCore,
  mlirCreateCIRCTConversionLowerSMTToZ3LLVM,
  mlirCreateCIRCTConversionLowerSeqToSV,
  mlirCreateCIRCTConversionLowerSimToSV,
  mlirCreateCIRCTConversionLowerVerifToSV,
  mlirCreateCIRCTConversionMaterializeCalyxToFSM,
  mlirCreateCIRCTConversionPipelineToHW,
  mlirCreateCIRCTConversionPrepareForEmission,
  mlirCreateCIRCTConversionSCFToCalyx,
  mlirCreateCIRCTConversionTestApplyLoweringOption
}
import org.llvm.mlir.scalalib.Pass

import java.lang.foreign.Arena

given ConversionCreateApi with
  def affineToLoopSchedule(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionAffineToLoopSchedule(arena))
  def cfToHandshake(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionCFToHandshake(arena))
  def calyxNative(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionCalyxNative(arena))
  def calyxRemoveGroupsFromFSM(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionCalyxRemoveGroupsFromFSM(arena))
  def calyxToFSM(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionCalyxToFSM(arena))
  def calyxToHW(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionCalyxToHW(arena))
  def convertAIGToComb(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionConvertAIGToComb(arena))
  def convertCombToAIG(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionConvertCombToAIG(arena))
  def convertCombToArith(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionConvertCombToArith(arena))
  def convertCombToSMT(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionConvertCombToSMT(arena))
  def convertFSMToSV(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionConvertFSMToSV(arena))
  def convertHWToBTOR2(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionConvertHWToBTOR2(arena))
  def convertHWToLLVM(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionConvertHWToLLVM(arena))
  def convertHWToSMT(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionConvertHWToSMT(arena))
  def convertHWToSystemC(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionConvertHWToSystemC(arena))
  def convertMooreToCore(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionConvertMooreToCore(arena))
  def convertToArcs(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionConvertToArcs(arena))
  def convertVerifToSMT(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionConvertVerifToSMT(arena))
  def dcToHW(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionDCToHW(arena))
  def exportChiselInterface(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionExportChiselInterface(arena))
  def exportSplitChiselInterface(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionExportSplitChiselInterface(arena))
  def exportSplitVerilog(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionExportSplitVerilog(arena))
  def exportVerilog(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionExportVerilog(arena))
  def hwArithToHW(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionHWArithToHW(arena))
  def hwLowerInstanceChoices(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionHWLowerInstanceChoices(arena))
  def handshakeRemoveBlock(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionHandshakeRemoveBlock(arena))
  def handshakeToDC(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionHandshakeToDC(arena))
  def handshakeToHW(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionHandshakeToHW(arena))
  def legalizeAnonEnums(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionLegalizeAnonEnums(arena))
  def loopScheduleToCalyx(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionLoopScheduleToCalyx(arena))
  def lowerArcToLLVM(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionLowerArcToLLVM(arena))
  def lowerFIRRTLToHW(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionLowerFIRRTLToHW(arena))
  def lowerFirMem(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionLowerFirMem(arena))
  def lowerHWToSV(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionLowerHWToSV(arena))
  def lowerLTLToCore(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionLowerLTLToCore(arena))
  def lowerSMTToZ3LLVM(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionLowerSMTToZ3LLVM(arena))
  def lowerSeqToSV(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionLowerSeqToSV(arena))
  def lowerSimToSV(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionLowerSimToSV(arena))
  def lowerVerifToSV(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionLowerVerifToSV(arena))
  def materializeCalyxToFSM(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionMaterializeCalyxToFSM(arena))
  def pipelineToHW(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionPipelineToHW(arena))
  def prepareForEmission(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionPrepareForEmission(arena))
  def scfToCalyx(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionSCFToCalyx(arena))
  def testApplyLoweringOption(
    using arena: Arena
  ): Pass = Pass(mlirCreateCIRCTConversionTestApplyLoweringOption(arena))
end given
