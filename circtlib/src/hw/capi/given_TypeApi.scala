// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.hw.capi

import org.llvm.circt.CAPI.hwArrayTypeGet
import org.llvm.circt.CAPI.hwArrayTypeGetElementType
import org.llvm.circt.CAPI.hwArrayTypeGetSize
import org.llvm.circt.CAPI.hwAttrIsAOutputFileAttr
import org.llvm.circt.CAPI.hwAttrIsAParamDeclAttr
import org.llvm.circt.CAPI.hwAttrIsAParamDeclRefAttr
import org.llvm.circt.CAPI.hwAttrIsAParamVerbatimAttr
import org.llvm.circt.CAPI.hwGetBitWidth
import org.llvm.circt.CAPI.hwInOutTypeGet
import org.llvm.circt.CAPI.hwOutputFileGetFileName
import org.llvm.circt.CAPI.hwOutputFileGetFromFileName
import org.llvm.circt.CAPI.hwParamDeclAttrGet
import org.llvm.circt.CAPI.hwParamDeclAttrGetName
import org.llvm.circt.CAPI.hwParamDeclAttrGetType
import org.llvm.circt.CAPI.hwParamDeclAttrGetValue
import org.llvm.circt.CAPI.hwParamDeclRefAttrGet
import org.llvm.circt.CAPI.hwParamDeclRefAttrGetName
import org.llvm.circt.CAPI.hwParamDeclRefAttrGetType
import org.llvm.circt.CAPI.hwParamVerbatimAttrGet
import org.llvm.circt.CAPI.{
  hwArrayTypeGet,
  hwArrayTypeGetSize,
  hwGetBitWidth,
  hwInOutTypeGetElementType,
  hwModuleTypeGet,
  hwModuleTypeGetInputName,
  hwModuleTypeGetInputType,
  hwModuleTypeGetNumInputs,
  hwModuleTypeGetNumOutputs,
  hwModuleTypeGetOutputName,
  hwModuleTypeGetOutputType,
  hwParamIntTypeGet,
  hwParamIntTypeGetWidthAttr,
  hwStructTypeGet,
  hwStructTypeGetField,
  hwStructTypeGetNumFields,
  hwTypeAliasTypeGet,
  hwTypeAliasTypeGetCanonicalType,
  hwTypeAliasTypeGetInnerType,
  hwTypeAliasTypeGetName,
  hwTypeAliasTypeGetScope,
  hwTypeIsAArrayType,
  hwTypeIsAInOut,
  hwTypeIsAIntType,
  hwTypeIsAModuleType,
  hwTypeIsAStructType,
  hwTypeIsATypeAliasType,
  hwTypeIsAValueType
}
import org.llvm.mlir.scalalib.StringRef
import org.llvm.mlir.scalalib.Type
import org.llvm.mlir.scalalib.{Module, Operation}
import org.llvm.mlir.scalalib.{Attribute, Context, given}

import java.lang.foreign.Arena
import java.lang.foreign.MemorySegment

given TypeApi with
  def arrayTypeGet(
    element:     Type,
    size:        Int
  )(
    using arena: Arena
  ): Type = Type(hwArrayTypeGet(arena, element.segment, size))
  extension (tpe: Type)
    def arrayTypeGetElementType(
      using arena: Arena
    ) = Type(hwArrayTypeGetElementType(arena, tpe.segment))
    def arrayTypeGetSize(): Int = hwArrayTypeGetSize(tpe.segment).toInt
    def getBitWidth():      Int = hwGetBitWidth(tpe.segment).toInt
    def inOutTypeGet(
    )(
      using arena: Arena
    ) = Type(hwInOutTypeGet(arena, tpe.segment))
    def inOutTypeGetElementType(
    )(
      using arena: Arena
    ) = Type(hwInOutTypeGetElementType(arena, tpe.segment))
  def moduleTypeGet(
    numPorts:    Int,
    ports:       Seq[HWModulePort]
  )(
    using arena: Arena,
    context:     Context
  ) = Type(hwModuleTypeGet(arena, context.segment, numPorts, ports.toMlirArray))
  extension (tpe: Type)
    def moduleTypeGetInputName(
      index:       Int
    )(
      using arena: Arena
    ): String = StringRef(hwModuleTypeGetInputName(arena, tpe.segment, index)).toScalaString
    def moduleTypeGetInputType(
      index:       Int
    )(
      using arena: Arena
    ): Type = Type(hwModuleTypeGetInputType(arena, tpe.segment, index))
    def moduleTypeGetNumInputs(): Int = hwModuleTypeGetNumInputs(tpe.segment).toInt
    def moduleTypeGetNumOutputs(
    )(
      using arena: Arena
    ): Int = hwModuleTypeGetNumOutputs(tpe.segment).toInt
    def moduleTypeGetOutputName(
      index:       Int
    )(
      using arena: Arena
    ): String = StringRef(hwModuleTypeGetOutputName(arena, tpe.segment, index)).toScalaString
    def moduleTypeGetOutputType(
      index:       Int
    )(
      using arena: Arena
    ): Type = Type(hwModuleTypeGetOutputType(arena, tpe.segment, index))
  def paramIntTypeGet(
    attribute:   Attribute
  )(
    using arena: Arena
  ): Type = Type(hwParamIntTypeGet(arena, attribute.segment))
  extension (tpe: Type)
    def paramIntTypeGetWidthAttr(
    )(
      using arena: Arena
    ): Attribute = Attribute(hwParamIntTypeGetWidthAttr(arena, tpe.segment))
  def structTypeGet(
    numElements: Int,
    elements:    Seq[HWStructFieldInfo]
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(hwStructTypeGet(arena, context.segment, numElements, elements.toMlirArray))
  extension (tpe: Type)
    def structTypeGetField(
      name:        String
    )(
      using arena: Arena
    ): Type = Type(hwStructTypeGetField(arena, tpe.segment, name.toStringRef.segment))
    def structTypeGetNumFields(
    )(
      using arena: Arena
    ): Int = hwStructTypeGetNumFields(tpe.segment).toInt
  def typeAliasTypeGet(
    scope:       String,
    name:        String,
    innerType:   Type
  )(
    using arena: Arena
  ): Type = Type(hwTypeAliasTypeGet(arena, scope.toStringRef.segment, name.toStringRef.segment, innerType.segment))
  extension (tpe: Type)
    def typeAliasTypeGetCanonicalType(
    )(
      using arena: Arena
    ): Type = Type(hwTypeAliasTypeGetCanonicalType(arena, tpe.segment))
    def typeAliasTypeGetInnerType(
    )(
      using arena: Arena
    ): Type = Type(hwTypeAliasTypeGetInnerType(arena, tpe.segment))
    def typeAliasTypeGetName(
    )(
      using arena: Arena
    ): String = StringRef(hwTypeAliasTypeGetName(arena, tpe.segment)).toScalaString
    def typeAliasTypeGetScope(
    )(
      using arena: Arena
    ): String = StringRef(hwTypeAliasTypeGetScope(arena, tpe.segment)).toScalaString
  extension (tpe: Type)
    def isArrayType():     Boolean = hwTypeIsAArrayType(tpe.segment)
    def isInOut():         Boolean = hwTypeIsAInOut(tpe.segment)
    def isIntType():       Boolean = hwTypeIsAIntType(tpe.segment)
    def isModuleType():    Boolean = hwTypeIsAModuleType(tpe.segment)
    def isStructType():    Boolean = hwTypeIsAStructType(tpe.segment)
    def isTypeAliasType(): Boolean = hwTypeIsATypeAliasType(tpe.segment)
    def isValueType():     Boolean = hwTypeIsAValueType(tpe.segment)
end given
