// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.exportverilog

import org.llvm.mlir.scalalib.capi.support.LogicalResult
import org.llvm.mlir.scalalib.capi.ir.Module

import java.lang.foreign.Arena

trait ExportVerilogApi:
  extension (module: Module)
    inline def exportVerilog(
      callback:    String => Unit
    )(
      using arena: Arena
    ): LogicalResult
    inline def exportSplitVerilog(
      directory:   String
    )(
      using arena: Arena
    ): LogicalResult
end ExportVerilogApi
