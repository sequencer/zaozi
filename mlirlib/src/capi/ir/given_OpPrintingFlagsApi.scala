// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.ir

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{
  mlirOpPrintingFlagsAssumeVerified,
  mlirOpPrintingFlagsCreate,
  mlirOpPrintingFlagsDestroy,
  mlirOpPrintingFlagsElideLargeElementsAttrs,
  mlirOpPrintingFlagsElideLargeResourceString,
  mlirOpPrintingFlagsEnableDebugInfo,
  mlirOpPrintingFlagsPrintGenericOpForm,
  mlirOpPrintingFlagsSkipRegions,
  mlirOpPrintingFlagsUseLocalScope
}

import java.lang.foreign.{Arena, MemorySegment}

given OpPrintingFlagsApi with
  inline def opPrintingFlagsCreate(
  )(
    using arena: Arena
  ): OpPrintingFlags = OpPrintingFlags(mlirOpPrintingFlagsCreate(arena))

  extension (opPrintingFlags: OpPrintingFlags)
    inline def flagsDestroy():                                             Unit          = mlirOpPrintingFlagsDestroy(opPrintingFlags.segment)
    inline def flagsElideLargeElementsAttrs(largeElementLimit: Long):      Unit          =
      mlirOpPrintingFlagsElideLargeElementsAttrs(opPrintingFlags.segment, largeElementLimit)
    inline def flagsElideLargeResourceString(largeResourceLimit: Long):    Unit          =
      mlirOpPrintingFlagsElideLargeResourceString(opPrintingFlags.segment, largeResourceLimit)
    inline def flagsEnableDebugInfo(enable: Boolean, prettyForm: Boolean): Unit          =
      mlirOpPrintingFlagsEnableDebugInfo(opPrintingFlags.segment, enable, prettyForm)
    inline def flagsPrintGenericOpForm():                                  Unit          = mlirOpPrintingFlagsPrintGenericOpForm(opPrintingFlags.segment)
    inline def flagsUseLocalScope():                                       Unit          = mlirOpPrintingFlagsUseLocalScope(opPrintingFlags.segment)
    inline def flagsAssumeVerified():                                      Unit          = mlirOpPrintingFlagsAssumeVerified(opPrintingFlags.segment)
    inline def flagsSkipRegions():                                         Unit          = mlirOpPrintingFlagsSkipRegions(opPrintingFlags.segment)
    inline def segment:                                                    MemorySegment = opPrintingFlags._segment
    inline def sizeOf:                                                     Int           = MlirOpPrintingFlags.sizeof().toInt
end given
