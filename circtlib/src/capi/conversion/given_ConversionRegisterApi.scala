// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.conversion

import org.llvm.circt.CAPI.{
  mlirRegisterCIRCTConversionAffineToLoopSchedule,
  mlirRegisterCIRCTConversionCFToHandshake,
  mlirRegisterCIRCTConversionCalyxNative,
  mlirRegisterCIRCTConversionCalyxRemoveGroupsFromFSM,
  mlirRegisterCIRCTConversionCalyxToFSM,
  mlirRegisterCIRCTConversionCalyxToHW,
  mlirRegisterCIRCTConversionConvertAIGToComb,
  mlirRegisterCIRCTConversionConvertCombToAIG,
  mlirRegisterCIRCTConversionConvertCombToArith,
  mlirRegisterCIRCTConversionConvertCombToSMT,
  mlirRegisterCIRCTConversionConvertFSMToSV,
  mlirRegisterCIRCTConversionConvertHWToBTOR2,
  mlirRegisterCIRCTConversionConvertHWToLLVM,
  mlirRegisterCIRCTConversionConvertHWToSMT,
  mlirRegisterCIRCTConversionConvertHWToSystemC,
  mlirRegisterCIRCTConversionConvertMooreToCore,
  mlirRegisterCIRCTConversionConvertToArcs,
  mlirRegisterCIRCTConversionConvertVerifToSMT,
  mlirRegisterCIRCTConversionDCToHW,
  mlirRegisterCIRCTConversionExportChiselInterface,
  mlirRegisterCIRCTConversionExportSplitChiselInterface,
  mlirRegisterCIRCTConversionExportSplitVerilog,
  mlirRegisterCIRCTConversionExportVerilog,
  mlirRegisterCIRCTConversionHWArithToHW,
  mlirRegisterCIRCTConversionHWLowerInstanceChoices,
  mlirRegisterCIRCTConversionHandshakeRemoveBlock,
  mlirRegisterCIRCTConversionHandshakeToDC,
  mlirRegisterCIRCTConversionHandshakeToHW,
  mlirRegisterCIRCTConversionLegalizeAnonEnums,
  mlirRegisterCIRCTConversionLoopScheduleToCalyx,
  mlirRegisterCIRCTConversionLowerArcToLLVM,
  mlirRegisterCIRCTConversionLowerFIRRTLToHW,
  mlirRegisterCIRCTConversionLowerFirMem,
  mlirRegisterCIRCTConversionLowerHWToSV,
  mlirRegisterCIRCTConversionLowerLTLToCore,
  mlirRegisterCIRCTConversionLowerSMTToZ3LLVM,
  mlirRegisterCIRCTConversionLowerSeqToSV,
  mlirRegisterCIRCTConversionLowerSimToSV,
  mlirRegisterCIRCTConversionLowerVerifToSV,
  mlirRegisterCIRCTConversionMaterializeCalyxToFSM,
  mlirRegisterCIRCTConversionPasses,
  mlirRegisterCIRCTConversionPipelineToHW,
  mlirRegisterCIRCTConversionPrepareForEmission,
  mlirRegisterCIRCTConversionSCFToCalyx,
  mlirRegisterCIRCTConversionTestApplyLoweringOption
}

given ConversionRegisterApi with
  def affineToLoopSchedule:       Unit = mlirRegisterCIRCTConversionAffineToLoopSchedule()
  def cfToHandshake:              Unit = mlirRegisterCIRCTConversionCFToHandshake()
  def calyxNative:                Unit = mlirRegisterCIRCTConversionCalyxNative()
  def calyxRemoveGroupsFromFSM:   Unit = mlirRegisterCIRCTConversionCalyxRemoveGroupsFromFSM()
  def calyxToFSM:                 Unit = mlirRegisterCIRCTConversionCalyxToFSM()
  def calyxToHW:                  Unit = mlirRegisterCIRCTConversionCalyxToHW()
  def convertAIGToComb:           Unit = mlirRegisterCIRCTConversionConvertAIGToComb()
  def convertCombToAIG:           Unit = mlirRegisterCIRCTConversionConvertCombToAIG()
  def convertCombToArith:         Unit = mlirRegisterCIRCTConversionConvertCombToArith()
  def convertCombToSMT:           Unit = mlirRegisterCIRCTConversionConvertCombToSMT()
  def convertFSMToSV:             Unit = mlirRegisterCIRCTConversionConvertFSMToSV()
  def convertHWToBTOR2:           Unit = mlirRegisterCIRCTConversionConvertHWToBTOR2()
  def convertHWToLLVM:            Unit = mlirRegisterCIRCTConversionConvertHWToLLVM()
  def convertHWToSMT:             Unit = mlirRegisterCIRCTConversionConvertHWToSMT()
  def convertHWToSystemC:         Unit = mlirRegisterCIRCTConversionConvertHWToSystemC()
  def convertMooreToCore:         Unit = mlirRegisterCIRCTConversionConvertMooreToCore()
  def convertToArcs:              Unit = mlirRegisterCIRCTConversionConvertToArcs()
  def convertVerifToSMT:          Unit = mlirRegisterCIRCTConversionConvertVerifToSMT()
  def dcToHW:                     Unit = mlirRegisterCIRCTConversionDCToHW()
  def exportChiselInterface:      Unit = mlirRegisterCIRCTConversionExportChiselInterface()
  def exportSplitChiselInterface: Unit = mlirRegisterCIRCTConversionExportSplitChiselInterface()
  def exportSplitVerilog:         Unit = mlirRegisterCIRCTConversionExportSplitVerilog()
  def exportVerilog:              Unit = mlirRegisterCIRCTConversionExportVerilog()
  def hwArithToHW:                Unit = mlirRegisterCIRCTConversionHWArithToHW()
  def hwLowerInstanceChoices:     Unit = mlirRegisterCIRCTConversionHWLowerInstanceChoices()
  def handshakeRemoveBlock:       Unit = mlirRegisterCIRCTConversionHandshakeRemoveBlock()
  def handshakeToDC:              Unit = mlirRegisterCIRCTConversionHandshakeToDC()
  def handshakeToHW:              Unit = mlirRegisterCIRCTConversionHandshakeToHW()
  def legalizeAnonEnums:          Unit = mlirRegisterCIRCTConversionLegalizeAnonEnums()
  def loopScheduleToCalyx:        Unit = mlirRegisterCIRCTConversionLoopScheduleToCalyx()
  def lowerArcToLLVM:             Unit = mlirRegisterCIRCTConversionLowerArcToLLVM()
  def lowerFIRRTLToHW:            Unit = mlirRegisterCIRCTConversionLowerFIRRTLToHW()
  def lowerFirMem:                Unit = mlirRegisterCIRCTConversionLowerFirMem()
  def lowerHWToSV:                Unit = mlirRegisterCIRCTConversionLowerHWToSV()
  def lowerLTLToCore:             Unit = mlirRegisterCIRCTConversionLowerLTLToCore()
  def lowerSMTToZ3LLVM:           Unit = mlirRegisterCIRCTConversionLowerSMTToZ3LLVM()
  def lowerSeqToSV:               Unit = mlirRegisterCIRCTConversionLowerSeqToSV()
  def lowerSimToSV:               Unit = mlirRegisterCIRCTConversionLowerSimToSV()
  def lowerVerifToSV:             Unit = mlirRegisterCIRCTConversionLowerVerifToSV()
  def materializeCalyxToFSM:      Unit = mlirRegisterCIRCTConversionMaterializeCalyxToFSM()
  def passes:                     Unit = mlirRegisterCIRCTConversionPasses()
  def pipelineToHW:               Unit = mlirRegisterCIRCTConversionPipelineToHW()
  def prepareForEmission:         Unit = mlirRegisterCIRCTConversionPrepareForEmission()
  def scfToCalyx:                 Unit = mlirRegisterCIRCTConversionSCFToCalyx()
  def testApplyLoweringOption:    Unit = mlirRegisterCIRCTConversionTestApplyLoweringOption()
end given
