// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package org.llvm.mlir.scalalib.capi.dialect.smt

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.mlirGetDialectHandle__smt__
import org.llvm.mlir.scalalib.capi.ir.{Context, DialectHandle, given}

import java.lang.foreign.Arena

given DialectApi with
  inline def loadDialect(
  )(
    using arena: Arena,
    context:     Context
  ): Unit =
    DialectHandle(mlirGetDialectHandle__smt__(arena)).loadDialect(
      using arena,
      context
    )
end given
