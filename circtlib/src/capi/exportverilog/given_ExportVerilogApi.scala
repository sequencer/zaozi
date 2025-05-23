// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.exportverilog

import org.llvm.circt.CAPI.{mlirExportSplitVerilog, mlirExportVerilog}
import org.llvm.mlir.scalalib.capi.support.{*, given}
import org.llvm.mlir.scalalib.capi.ir.{Module, given}

import java.lang.foreign.{Arena, MemorySegment}

given ExportVerilogApi with
  extension (module: Module)
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
