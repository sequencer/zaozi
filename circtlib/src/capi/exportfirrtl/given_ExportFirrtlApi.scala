// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.exportfirrtl

import org.llvm.circt.CAPI.mlirExportFIRRTL
import org.llvm.mlir.scalalib.capi.support.{*, given}
import org.llvm.mlir.scalalib.capi.ir.{Module, given}

import java.lang.foreign.{Arena, MemorySegment}

given ExportFirrtlApi with
  extension (module: Module)
    inline def exportFIRRTL(
      callback:    String => Unit
    )(
      using arena: Arena
    ): LogicalResult = LogicalResult(
      mlirExportFIRRTL(arena, module.segment, callback.stringToStringCallback.segment, MemorySegment.NULL)
    )
end given
