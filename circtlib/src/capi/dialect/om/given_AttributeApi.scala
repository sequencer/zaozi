// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Yuhang Zeng <unlsycn@unlsycn.com>
package org.llvm.circt.scalalib.capi.dialect.om

import org.llvm.circt.CAPI.{
  omAttrIsAIntegerAttr,
  omAttrIsAListAttr,
  omAttrIsAMapAttr,
  omAttrIsAReferenceAttr,
  omIntegerAttrGet,
  omIntegerAttrGetInt,
  omIntegerAttrToString,
  omListAttrGetElement,
  omListAttrGetNumElements,
  omMapAttrGetElementKey,
  omMapAttrGetElementValue,
  omMapAttrGetNumElements,
  omReferenceAttrGetInnerRef
}
import org.llvm.mlir.scalalib.capi.ir.{Attribute, Identifier, given}

import java.lang.foreign.Arena

given AttributeApi with
  extension (attr: Attribute)
    inline def isIntegerAttr:          Boolean = omAttrIsAIntegerAttr(attr.segment)
    inline def isListAttr:             Boolean = omAttrIsAListAttr(attr.segment)
    inline def isMapAttr:              Boolean = omAttrIsAMapAttr(attr.segment)
    inline def isReferenceAttr:        Boolean = omAttrIsAReferenceAttr(attr.segment)
    inline def integerAttrGet(
      using arena: Arena
    ): Attribute = Attribute(omIntegerAttrGet(arena, attr.segment))
    inline def integerAttrGetInt(
      using arena: Arena
    ): Attribute = Attribute(omIntegerAttrGetInt(arena, attr.segment))
    inline def integerAttrToString(
      using arena: Arena
    ): String = omIntegerAttrToString(arena, attr.segment).toString
    inline def listAttrGetElement(
      pos:         Int
    )(
      using arena: Arena
    ): Attribute = Attribute(omListAttrGetElement(arena, attr.segment, pos))
    inline def listAttrGetNumElements: Int     = omListAttrGetNumElements(attr.segment).toInt
    inline def mapAttrGetElementKey(
      pos:         Int
    )(
      using arena: Arena
    ): Identifier = Identifier(omMapAttrGetElementKey(arena, attr.segment, pos))
    inline def mapAttrGetElementValue(
      pos:         Int
    )(
      using arena: Arena
    ): Attribute = Attribute(omMapAttrGetElementValue(arena, attr.segment, pos))
    inline def mapAttrGetNumElements:  Int     = omMapAttrGetNumElements(attr.segment).toInt
    inline def referenceAttrGetInnerRef(
      using arena: Arena
    ): Attribute = Attribute(omReferenceAttrGetInnerRef(arena, attr.segment))
end given
