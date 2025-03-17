// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Yuhang Zeng <unlsycn@unlsycn.com>
package org.llvm.circt.scalalib.hw.capi

import org.llvm.mlir.scalalib.{Attribute, Context, DialectHandle, Identifier, Location, Module, Type, TypeID, given}
import org.llvm.circt.*
import org.llvm.circt.CAPI.*

import java.lang.foreign.{Arena, MemorySegment}

given AttributeApi with
  inline def innerSymAttrGet(
    symName:     Attribute
  )(
    using arena: Arena
  ): Attribute =
    Attribute(
      hwInnerSymAttrGet(
        arena,
        symName.segment
      )
    )
  inline def innerSymAttrGet(
    symName:     String
  )(
    using arena: Arena,
    context:     Context
  ): Attribute = innerSymAttrGet(symName.stringAttrGet)

  inline def innerSymAttrGetEmpty(
    using arena: Arena,
    context:     Context
  ): Attribute =
    Attribute(hwInnerSymAttrGetEmpty(arena, context.segment))

  inline def innerRefAttrGet(
    moduleName:  Attribute,
    innerSym:    Attribute
  )(
    using arena: Arena,
    context:     Context
  ): Attribute =
    Attribute(
      hwInnerRefAttrGet(
        arena,
        moduleName.segment,
        innerSym.segment
      )
    )
  inline def innerRefAttrGet(
    moduleName:  Attribute | String,
    innerSym:    Attribute | String
  )(
    using arena: Arena,
    context:     Context
  ): Attribute = innerRefAttrGet(
    moduleName match
      case stringAttr: Attribute => stringAttr
      case string:     String    => string.stringAttrGet
    ,
    innerSym match
      case stringAttr: Attribute => stringAttr
      case string:     String    => string.stringAttrGet
  )

  extension (attr: Attribute)
    inline def isAInnerSymAttr: Boolean =
      hwAttrIsAInnerSymAttr(attr.segment)

    inline def innerSymAttrGetSymName(
      using arena: Arena
    ): Attribute =
      Attribute(hwInnerSymAttrGetSymName(arena, attr.segment))

    inline def isAInnerRefAttr: Boolean = hwAttrIsAInnerRefAttr(attr.segment)

    inline def innerRefAttrGetName(
      using arena: Arena
    ): Attribute =
      Attribute(hwInnerRefAttrGetName(arena, attr.segment))

    inline def innerRefAttrGetModule(
      using arena: Arena
    ): Attribute =
      Attribute(hwInnerRefAttrGetModule(arena, attr.segment))
end given
