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

given AttributeApi with
  extension (firrtlConvention:      FirrtlConvention)
    inline def toAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(firrtlAttrGetConvention(arena, context.segment, firrtlConvention.toNative))
  extension (ref:                   FirrtlEventControl)
    inline def attrGetEventControl(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(
      firrtlAttrGetEventControl(arena, context.segment, ref.toNative)
    )
  extension (bigInt:                BigInt)
    inline def attrGetIntegerFromString(
      tpe:         Type,
      width:       Option[Int] = None
    )(
      using arena: Arena
    ): Attribute =
      Attribute(
        firrtlAttrGetIntegerFromString(
          arena,
          tpe.segment,
          width.getOrElse(tpe.integerTypeGetWidth.toInt),
          bigInt.toString(10).toStringRef.segment,
          10
        )
      )
  extension (firrtlLayerConvention: FirrtlLayerConvention)
    inline def toAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(firrtlAttrGetLayerConvention(arena, context.segment, firrtlLayerConvention.toNative))
  extension (memDir:                FirrtlMemDir)
    inline def toAttribute(
      using arena: Arena,
      context:     Context
    ): MemorySegment = firrtlAttrGetMemDir(arena, context.segment, memDir.toNative)
  inline def getMemInit(
    filename:    String,
    isBinary:    Boolean,
    isInline:    Boolean
  )(
    using arena: Arena,
    context:     Context
  ): Attribute = Attribute(
    firrtlAttrGetMemInit(
      arena,
      context.segment,
      filename.identifierGet.segment,
      isBinary,
      isInline
    )
  )
  extension (ref:                   FirrtlNameKind)
    inline def attrGetNameKind(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(firrtlAttrGetNameKind(arena, context.segment, ref.toNative))
  extension (value:                 String)
    inline def getParamDeclAttribute(
      name:        String,
      tpe:         Type
    )(
      using arena: Arena,
      context:     Context
    ): Attribute =
      Attribute(
        firrtlAttrGetParamDecl(
          arena,
          context.segment,
          name.identifierGet.segment,
          tpe.segment,
          value.stringAttrGet.segment
        )
      )
  extension (value:                 BigInt)
    inline def getParamDeclAttribute(
      name:        String,
      tpe:         Type
    )(
      using arena: Arena,
      context:     Context
    ): Attribute =
      Attribute(
        firrtlAttrGetParamDecl(
          arena,
          context.segment,
          name.identifierGet.segment,
          tpe.segment,
          value.attrGetIntegerFromString(value.bitLength.integerTypeGet).segment
        )
      )
  extension (value:                 Double)
    inline def getParamDeclAttribute(
      name:        String,
      tpe:         Type
    )(
      using arena: Arena,
      context:     Context
    ): Attribute =
      Attribute(
        firrtlAttrGetParamDecl(
          arena,
          context.segment,
          name.identifierGet.segment,
          tpe.segment,
          value.floatAttrDoubleGet(summon[org.llvm.mlir.scalalib.TypeApi].f64TypeGet).segment
        )
      )
  extension (portDirections:        Seq[FirrtlDirection])
    inline def attrGetPortDirs(
      using arena: Arena,
      context:     Context
    ): Attribute =
      Attribute(firrtlAttrGetPortDirs(arena, context.segment, portDirections.size, portDirections.toMlirArray))
  extension (ruw:                   FirrtlRUW)
    inline def toAttribute(
      using arena: Arena,
      context:     Context
    ): MemorySegment = firrtlAttrGetRUW(arena, context.segment, ruw.toNative)
end given
