// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.dialect.llhd

import org.llvm.circt.CAPI.{
  llhdPointerTypeGet,
  llhdPointerTypeGetElementType,
  llhdSignalTypeGet,
  llhdSignalTypeGetElementType,
  llhdTypeIsAPointerType,
  llhdTypeIsASignalType,
  llhdTypeIsATimeType
}
import org.llvm.mlir.scalalib.capi.ir.{Type, given}

import java.lang.foreign.Arena

given TypeApi with
  inline def pointerTypeGet(
    element:     Type
  )(
    using arena: Arena
  ): Type = Type(llhdPointerTypeGet(arena, element.segment))
  extension (tpe: Type)
    inline def pointerTypeGetElementType(
    )(
      using arena: Arena
    ): Type = Type(llhdPointerTypeGetElementType(arena, tpe.segment))
    inline def signalTypeGet(
    )(
      using arena: Arena
    ): Type = Type(llhdSignalTypeGet(arena, tpe.segment))
    inline def signalTypeGetElementType(
    )(
      using arena: Arena
    ): Type = Type(llhdSignalTypeGetElementType(arena, tpe.segment))
    inline def isPointerType: Boolean = llhdTypeIsAPointerType(tpe.segment)
    inline def isSignalType:  Boolean = llhdTypeIsASignalType(tpe.segment)
    inline def isTimeType:    Boolean = llhdTypeIsATimeType(tpe.segment)
end given
