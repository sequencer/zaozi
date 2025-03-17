// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Yuhang Zeng <unlsycn@unlsycn.com>
package org.llvm.circt.scalalib.hw.capi

import org.llvm.mlir.scalalib.*

import java.lang.foreign.{Arena, MemorySegment}

trait AttributeApi:
  inline def innerSymAttrGet(
    symName:     Attribute
  )(
    using arena: Arena
  ): Attribute
  inline def innerSymAttrGetEmpty(
    using arena: Arena,
    context:     Context
  ): Attribute

  inline def innerRefAttrGet(
    moduleName:  Attribute,
    innerSym:    Attribute
  )(
    using arena: Arena,
    context:     Context
  ): Attribute

  extension (attr: Attribute)
    inline def isAInnerSymAttr: Boolean
    inline def innerSymAttrGetSymName(
      using arena: Arena
    ):                          Attribute

    inline def isAInnerRefAttr: Boolean
    inline def innerRefAttrGetName(
      using arena: Arena
    ):                          Attribute
    inline def innerRefAttrGetModule(
      using arena: Arena
    ):                          Attribute

end AttributeApi
