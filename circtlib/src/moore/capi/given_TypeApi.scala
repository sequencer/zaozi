// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.moore.capi

import org.llvm.circt.CAPI.mooreArrayTypeGet
import org.llvm.circt.CAPI.mooreAssocArrayTypeGet
import org.llvm.circt.CAPI.mooreChandleTypeGet
import org.llvm.circt.CAPI.mooreEventTypeGet
import org.llvm.circt.CAPI.mooreIntTypeGetInt
import org.llvm.circt.CAPI.mooreIntTypeGetLogic
import org.llvm.circt.CAPI.mooreIsFourValuedType
import org.llvm.circt.CAPI.mooreIsTwoValuedType
import org.llvm.circt.CAPI.mooreOpenArrayTypeGet
import org.llvm.circt.CAPI.mooreOpenUnpackedArrayTypeGet
import org.llvm.circt.CAPI.mooreQueueTypeGet
import org.llvm.circt.CAPI.mooreRealTypeGet
import org.llvm.circt.CAPI.mooreStringTypeGet
import org.llvm.circt.CAPI.mooreUnpackedArrayTypeGet
import org.llvm.circt.CAPI.mooreVoidTypeGet
import org.llvm.mlir.scalalib.Type
import org.llvm.mlir.scalalib.{Context, DialectHandle, given}

import java.lang.foreign.Arena

given TypeApi with
  inline def arrayTypeGet(
    size:        Int,
    elementType: Type
  )(
    using arena: Arena
  ): Type = Type(mooreArrayTypeGet(arena, size, elementType.segment))
  inline def assocArrayTypeGet(
    elementType: Type,
    indexType:   Type
  )(
    using arena: Arena
  ): Type = Type(mooreAssocArrayTypeGet(arena, elementType.segment, indexType.segment))
  inline def chandleTypeGet(
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(mooreChandleTypeGet(arena, context.segment))
  inline def eventTypeGet(
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(mooreEventTypeGet(arena, context.segment))
  inline def intTypeGetInt(
    width:       Int
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(mooreIntTypeGetInt(arena, context.segment, width))
  inline def intTypeGetLogic(
    width:       Int
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(mooreIntTypeGetLogic(arena, context.segment, width))
  extension (tpe: Type)
    inline def isFourValuedType(): Boolean = mooreIsFourValuedType(tpe.segment)
    inline def isTwoValuedType():  Boolean = mooreIsTwoValuedType(tpe.segment)
  inline def openArrayTypeGet(
    elementType: Type
  )(
    using arena: Arena
  ): Type = Type(mooreOpenArrayTypeGet(arena, elementType.segment))
  inline def openUnpackedArrayTypeGet(
    elementType: Type
  )(
    using arena: Arena
  ): Type = Type(mooreOpenUnpackedArrayTypeGet(arena, elementType.segment))
  inline def queueTypeGet(
    elementType: Type,
    bound:       Int
  )(
    using arena: Arena
  ): Type = Type(mooreQueueTypeGet(arena, elementType.segment, bound))
  inline def realTypeGet(
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(mooreRealTypeGet(arena, context.segment))
  inline def stringTypeGet(
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(mooreStringTypeGet(arena, context.segment))
  inline def unpackedArrayTypeGet(
    size:        Int,
    elementType: Type
  )(
    using arena: Arena
  ): Type = Type(mooreUnpackedArrayTypeGet(arena, size, elementType.segment))
  inline def voidTypeGet(
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(mooreVoidTypeGet(arena, context.segment))
end given
