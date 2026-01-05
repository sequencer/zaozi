// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package org.llvm.mlir.scalalib.capi.dialect.smt

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{
  mlirSMTAttrCheckBVCmpPredicate,
  mlirSMTAttrCheckIntPredicate,
  mlirSMTAttrGetBVCmpPredicate,
  mlirSMTAttrGetBitVector,
  mlirSMTAttrGetIntPredicate,
  mlirSMTAttrIsASMTAttribute
}
import org.llvm.mlir.scalalib.capi.support.{*, given}
import org.llvm.mlir.scalalib.capi.ir.{Attribute, Context, given}

import java.lang.foreign.Arena

given AttributeApi with
  extension (str:   String)
    inline def getBVCmpPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(mlirSMTAttrGetBVCmpPredicate(arena, context.segment, str.toStringRef.segment))
    inline def getIntPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(mlirSMTAttrGetIntPredicate(arena, context.segment, str.toStringRef.segment))
  extension (value: Int)
    inline def getBitVectorAttribute(
      width:       Int
    )(
      using arena: Arena,
      context:     Context
    ): Attribute =
      require(
        width >= (if value == 0 then 1 else 32 - Integer.numberOfLeadingZeros(value)),
        s"Width $width is insufficient to represent unsigned value $value"
      )
      Attribute(mlirSMTAttrGetBitVector(arena, context.segment, value, width))
  extension (attr:  Attribute) inline def isSMTAttribute: Boolean = mlirSMTAttrIsASMTAttribute(attr.segment)

  extension (str: String)
    inline def checkBVCmpPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Boolean = mlirSMTAttrCheckBVCmpPredicate(context.segment, str.toStringRef.segment)
    inline def checkIntPredicateAttribute(
      using arena: Arena,
      context:     Context
    ): Boolean = mlirSMTAttrCheckIntPredicate(context.segment, str.toStringRef.segment)
end given
