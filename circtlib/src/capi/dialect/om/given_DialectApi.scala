// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Yuhang Zeng <unlsycn@unlsycn.com>
package org.llvm.circt.scalalib.capi.dialect.om

import org.llvm.circt.CAPI.mlirGetDialectHandle__om__ as mlirGetDialectHandle
import org.llvm.mlir.scalalib.given
import org.llvm.mlir.scalalib.{Context, DialectHandle}

import java.lang.foreign.Arena

given DialectApi with
  inline def loadDialect(
    using arena: Arena,
    context:     Context
  ): Unit =
    DialectHandle(mlirGetDialectHandle(arena)).loadDialect(
      using arena,
      context
    )
end given
