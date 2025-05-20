// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.exportfirrtl

import org.llvm.mlir.scalalib.{LogicalResult, Module}

import java.lang.foreign.Arena

trait ExportFirrtlApi:
  extension (module: Module)
    inline def exportFIRRTL(
      callback:    String => Unit
    )(
      using arena: Arena
    ): LogicalResult
end ExportFirrtlApi
