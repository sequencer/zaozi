// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Yuhang Zeng <unlsycn@unlsycn.com>
package org.llvm.circt.scalalib.capi.dialect.om

import org.llvm.circt.*
import org.llvm.circt.CAPI.{
  omAnyTypeGetTypeID,
  omClassTypeGetName,
  omClassTypeGetTypeID,
  omFrozenBasePathTypeGetTypeID,
  omFrozenPathTypeGetTypeID,
  omListTypeGetElementType,
  omListTypeGetTypeID,
  omTypeIsAAnyType,
  omTypeIsAClassType,
  omTypeIsAFrozenBasePathType,
  omTypeIsAFrozenPathType,
  omTypeIsAListType,
  omTypeIsAStringType
}

import org.llvm.mlir.scalalib.capi.support.{*, given}
import org.llvm.mlir.scalalib.capi.ir.{Identifier, Type, given}

import java.lang.foreign.Arena

given TypeApi with
  inline def anyTypeGetTypeID(
    using arena: Arena
  ): TypeID = TypeID(omAnyTypeGetTypeID(arena))
  extension (tpe: Type)
    inline def classTypeGetName(
      using arena: Arena
    ): Identifier = Identifier(omClassTypeGetName(arena, tpe.segment))
  inline def classTypeGetTypeID(
    using arena: Arena
  ): TypeID = TypeID(omClassTypeGetTypeID(arena))
  inline def frozenBasePathTypeGetTypeID(
    using arena: Arena
  ): TypeID = TypeID(omFrozenBasePathTypeGetTypeID(arena))
  inline def frozenPathTypeGetTypeID(
    using arena: Arena
  ): TypeID = TypeID(omFrozenPathTypeGetTypeID(arena))
  extension (tpe: Type)
    inline def listTypeGetElementType(
      using arena: Arena
    ): Type = Type(omListTypeGetElementType(arena, tpe.segment))
  inline def listTypeGetTypeID(
    using arena: Arena
  ): TypeID = TypeID(omListTypeGetTypeID(arena))
  extension (tpe: Type)
    inline def isAnyType:            Boolean = omTypeIsAAnyType(tpe.segment)
    inline def isClassType:          Boolean = omTypeIsAClassType(tpe.segment)
    inline def isFrozenBasePathType: Boolean = omTypeIsAFrozenBasePathType(tpe.segment)
    inline def isFrozenPathType:     Boolean = omTypeIsAFrozenPathType(tpe.segment)
    inline def isListType:           Boolean = omTypeIsAListType(tpe.segment)
    inline def isStringType:         Boolean = omTypeIsAStringType(tpe.segment)
end given
