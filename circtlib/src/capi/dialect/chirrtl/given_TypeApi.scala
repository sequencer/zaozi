// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.dialect.chirrtl

import org.llvm.circt.CAPI.{chirrtlTypeGetCMemory, chirrtlTypeGetCMemoryPort}
import org.llvm.mlir.scalalib.capi.ir.{Context, Type, given}

import java.lang.foreign.Arena

given TypeApi with
  inline def getCMemory(
    elementType: Type,
    numElements: Int
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(chirrtlTypeGetCMemory(arena, context.segment, elementType.segment, numElements))
  inline def getCMemoryPort(
    using arena: Arena,
    context:     Context
  ): Type = Type(chirrtlTypeGetCMemoryPort(arena, context.segment))
end given
