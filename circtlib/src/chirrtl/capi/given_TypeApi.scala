// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.chirrtl.capi

import org.llvm.circt.CAPI.{chirrtlTypeGetCMemory, chirrtlTypeGetCMemoryPort}
import org.llvm.mlir.scalalib.given
import org.llvm.mlir.scalalib.{Context, Type}

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
