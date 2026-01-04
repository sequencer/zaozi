// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.conversion

import org.llvm.mlir.scalalib.capi.pass.Pass

import java.lang.foreign.Arena

trait ConversionCreateApi:
  def affineToLoopSchedule(
    using arena: Arena
  ): Pass
  def cfToHandshake(
    using arena: Arena
  ): Pass
  def calyxNative(
    using arena: Arena
  ): Pass
  def calyxRemoveGroupsFromFSM(
    using arena: Arena
  ): Pass
  def calyxToFSM(
    using arena: Arena
  ): Pass
  def calyxToHW(
    using arena: Arena
  ): Pass
  def convertCombToArith(
    using arena: Arena
  ): Pass
  def convertCombToSMT(
    using arena: Arena
  ): Pass
  def convertFSMToSV(
    using arena: Arena
  ): Pass
  def convertHWToBTOR2(
    using arena: Arena
  ): Pass
  def convertHWToLLVM(
    using arena: Arena
  ): Pass
  def convertHWToSMT(
    using arena: Arena
  ): Pass
  def convertHWToSystemC(
    using arena: Arena
  ): Pass
  def convertMooreToCore(
    using arena: Arena
  ): Pass
  def convertVerifToSMT(
    using arena: Arena
  ): Pass
  def dcToHW(
    using arena: Arena
  ): Pass
  def exportSplitVerilog(
    using arena: Arena
  ): Pass
  def exportVerilog(
    using arena: Arena
  ): Pass
  def hwArithToHW(
    using arena: Arena
  ): Pass
  def hwLowerInstanceChoices(
    using arena: Arena
  ): Pass
  def handshakeRemoveBlock(
    using arena: Arena
  ): Pass
  def handshakeToDC(
    using arena: Arena
  ): Pass
  def handshakeToHW(
    using arena: Arena
  ): Pass
  def legalizeAnonEnums(
    using arena: Arena
  ): Pass
  def loopScheduleToCalyx(
    using arena: Arena
  ): Pass
  def lowerArcToLLVM(
    using arena: Arena
  ): Pass
  def lowerFIRRTLToHW(
    using arena: Arena
  ): Pass
  def lowerFirMem(
    using arena: Arena
  ): Pass
  def lowerHWToSV(
    using arena: Arena
  ): Pass
  def lowerLTLToCore(
    using arena: Arena
  ): Pass
  def lowerSMTToZ3LLVM(
    using arena: Arena
  ): Pass
  def lowerSeqToSV(
    using arena: Arena
  ): Pass
  def lowerSimToSV(
    using arena: Arena
  ): Pass
  def lowerVerifToSV(
    using arena: Arena
  ): Pass
  def materializeCalyxToFSM(
    using arena: Arena
  ): Pass
  def pipelineToHW(
    using arena: Arena
  ): Pass
  def prepareForEmission(
    using arena: Arena
  ): Pass
  def scfToCalyx(
    using arena: Arena
  ): Pass
  def testApplyLoweringOption(
    using arena: Arena
  ): Pass
end ConversionCreateApi

trait ConversionRegisterApi:
  def affineToLoopSchedule:     Unit
  def cfToHandshake:            Unit
  def calyxNative:              Unit
  def calyxRemoveGroupsFromFSM: Unit
  def calyxToFSM:               Unit
  def calyxToHW:                Unit
  def convertCombToArith:       Unit
  def convertCombToSMT:         Unit
  def convertFSMToSV:           Unit
  def convertHWToBTOR2:         Unit
  def convertHWToLLVM:          Unit
  def convertHWToSMT:           Unit
  def convertHWToSystemC:       Unit
  def convertMooreToCore:       Unit
  def convertVerifToSMT:        Unit
  def dcToHW:                   Unit
  def exportSplitVerilog:       Unit
  def exportVerilog:            Unit
  def hwArithToHW:              Unit
  def hwLowerInstanceChoices:   Unit
  def handshakeRemoveBlock:     Unit
  def handshakeToDC:            Unit
  def handshakeToHW:            Unit
  def legalizeAnonEnums:        Unit
  def loopScheduleToCalyx:      Unit
  def lowerArcToLLVM:           Unit
  def lowerFIRRTLToHW:          Unit
  def lowerFirMem:              Unit
  def lowerHWToSV:              Unit
  def lowerLTLToCore:           Unit
  def lowerSMTToZ3LLVM:         Unit
  def lowerSeqToSV:             Unit
  def lowerSimToSV:             Unit
  def lowerVerifToSV:           Unit
  def materializeCalyxToFSM:    Unit
  def passes:                   Unit
  def pipelineToHW:             Unit
  def prepareForEmission:       Unit
  def scfToCalyx:               Unit
  def testApplyLoweringOption:  Unit
end ConversionRegisterApi
