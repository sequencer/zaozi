// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

// circt-c/Dialect/Moore.h
package org.llvm.circt.scalalib.capi.dialect.moore

import org.llvm.mlir.scalalib.*

import java.lang.foreign.Arena

/** Arc Dialect Api
  * {{{
  * mlirGetDialectHandle__moore__
  * }}}
  */
trait DialectApi:
  inline def loadDialect(
    using arena: Arena,
    context:     Context
  ): Unit
end DialectApi

/** Moore Type API
  * {{{
  * mooreArrayTypeGet
  * mooreAssocArrayTypeGet
  * mooreChandleTypeGet
  * mooreEventTypeGet
  * mooreIntTypeGetInt
  * mooreIntTypeGetLogic
  * mooreIsFourValuedType
  * mooreIsTwoValuedType
  * mooreOpenArrayTypeGet
  * mooreOpenUnpackedArrayTypeGet
  * mooreQueueTypeGet
  * mooreRealTypeGet
  * mooreStringTypeGet
  * mooreUnpackedArrayTypeGet
  * mooreVoidTypeGet
  * }}}
  */
trait TypeApi:
  inline def arrayTypeGet(
    size:        Int,
    elementType: Type
  )(
    using arena: Arena
  ): Type
  inline def assocArrayTypeGet(
    elementType: Type,
    indexType:   Type
  )(
    using arena: Arena
  ): Type
  inline def chandleTypeGet(
    using arena: Arena,
    context:     Context
  ): Type
  inline def eventTypeGet(
    using arena: Arena,
    context:     Context
  ): Type
  inline def intTypeGetInt(
    width:       Int
  )(
    using arena: Arena,
    context:     Context
  ): Type
  inline def intTypeGetLogic(
    width:       Int
  )(
    using arena: Arena,
    context:     Context
  ): Type
  extension (tpe: Type)
    inline def isFourValuedType(): Boolean
    inline def isTwoValuedType():  Boolean
  inline def openArrayTypeGet(
    elementType: Type
  )(
    using arena: Arena
  ): Type
  inline def openUnpackedArrayTypeGet(
    elementType: Type
  )(
    using arena: Arena
  ): Type
  inline def queueTypeGet(
    elementType: Type,
    bound:       Int
  )(
    using arena: Arena
  ): Type
  inline def realTypeGet(
    using arena: Arena,
    context:     Context
  ): Type
  inline def stringTypeGet(
    using arena: Arena,
    context:     Context
  ): Type
  inline def unpackedArrayTypeGet(
    size:        Int,
    elementType: Type
  )(
    using arena: Arena
  ): Type
  inline def voidTypeGet(
    using arena: Arena,
    context:     Context
  ): Type
end TypeApi
