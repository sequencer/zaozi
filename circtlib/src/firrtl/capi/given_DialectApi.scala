// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.firrtl.capi

import org.llvm.circt.*
import org.llvm.circt.CAPI.{mlirGetDialectHandle__firrtl__ as mlirGetDialectHandle, *}
import org.llvm.mlir.scalalib.{
  given_AttributeApi,
  Attribute,
  Context,
  DialectHandle,
  Identifier,
  LogicalResult,
  Module,
  PassManager,
  Type,
  Value,
  given
}

import java.lang.foreign.{Arena, MemorySegment}

given DialectApi with
  extension (context: Context)
    inline def loadDialect(
    )(
      using arena: Arena
    ): Unit =
      DialectHandle(mlirGetDialectHandle(arena)).loadDialect(
        using arena,
        context
      )
end given
