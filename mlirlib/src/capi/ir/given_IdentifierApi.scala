// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.ir

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{mlirIdentifierGet, mlirIdentifierGetContext, mlirIdentifierStr}
import org.llvm.mlir.scalalib.capi.support.{*, given}

import java.lang.foreign.{Arena, MemorySegment}

given IdentifierApi with
  extension (identifierString: String)
    inline def identifierGet(
      using arena: Arena,
      context:     Context
    ): Identifier =
      Identifier(mlirIdentifierGet(arena, context._segment, identifierString.toStringRef.segment))
  extension (identifier:       Identifier)
    inline def getContext(
      using arena: Arena
    ): Context = Context(mlirIdentifierGetContext(arena, identifier.segment))
    inline def str(
      using arena: Arena
    ): String = StringRef(mlirIdentifierStr(arena, identifier.segment)).toScalaString
    inline def segment: MemorySegment = identifier._segment
    inline def sizeOf:  Int           = MlirIdentifier.sizeof().toInt
end given
