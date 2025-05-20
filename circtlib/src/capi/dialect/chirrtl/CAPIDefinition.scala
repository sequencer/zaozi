// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

// circt-c/Dialect/Chirrtl.h
package org.llvm.circt.scalalib.capi.dialect.chirrtl

import org.llvm.mlir.scalalib.{Context, Type}

import java.lang.foreign.Arena

/** Chirrtl Dialect API
  *
  * {{{
  * mlirGetDialectHandle__chirrtl__
  * }}}
  */
trait DialectApi:
  inline def loadDialect(
    using arena: Arena,
    context:     Context
  ): Unit
end DialectApi

/** Chirrtl Type API
  *
  * {{{
  * chirrtlTypeGetCMemory
  * chirrtlTypeGetCMemoryPort
  * }}}
  */
trait TypeApi:
  inline def getCMemory(
    elementType: Type,
    numElements: Int
  )(
    using arena: Arena,
    context:     Context
  ): Type
  inline def getCMemoryPort(
    using arena: Arena,
    context:     Context
  ): Type
end TypeApi
