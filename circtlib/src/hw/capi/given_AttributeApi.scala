// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.hw.capi

import org.llvm.circt.CAPI.hwAttrIsAOutputFileAttr
import org.llvm.circt.CAPI.hwAttrIsAParamDeclAttr
import org.llvm.circt.CAPI.hwAttrIsAParamDeclRefAttr
import org.llvm.circt.CAPI.hwAttrIsAParamVerbatimAttr
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
  hwAttrIsAInnerRefAttr,
  hwAttrIsAInnerSymAttr,
  hwInnerRefAttrGet,
  hwInnerRefAttrGetModule,
  hwInnerRefAttrGetName,
  hwInnerSymAttrGet,
  hwInnerSymAttrGetEmpty,
  hwInnerSymAttrGetSymName,
  hwInstanceGraphDestroy,
  hwInstanceGraphForEachNode,
  hwInstanceGraphGet,
  hwInstanceGraphGetTopLevelNode,
  hwInstanceGraphNodeEqual,
  hwInstanceGraphNodeGetModule,
  hwInstanceGraphNodeGetModuleOp
}
import org.llvm.mlir.scalalib.StringRef
import org.llvm.mlir.scalalib.Type
import org.llvm.mlir.scalalib.{Module, Operation}
import org.llvm.mlir.scalalib.{Attribute, Context, given}

import java.lang.foreign.Arena
import java.lang.foreign.MemorySegment

given AttributeApi with
  extension (attr: Attribute)
    inline def isInnerRefAttr:      Boolean = hwAttrIsAInnerRefAttr(attr.segment)
    inline def isInnerSymAttr:      Boolean = hwAttrIsAInnerSymAttr(attr.segment)
    inline def isOutputFileAttr:    Boolean = hwAttrIsAOutputFileAttr(attr.segment)
    inline def isParamDeclAttr:     Boolean = hwAttrIsAParamDeclAttr(attr.segment)
    inline def isParamDeclRefAttr:  Boolean = hwAttrIsAParamDeclRefAttr(attr.segment)
    inline def isParamVerbatimAttr: Boolean = hwAttrIsAParamVerbatimAttr(attr.segment)
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
    moduleName:  String,
    innerSym:    String
  )(
    using arena: Arena,
    context:     Context
  ): Attribute = innerRefAttrGet(
    moduleName.stringAttrGet,
    innerSym.stringAttrGet
  )
  extension (attr: Attribute)
    inline def innerRefAttrGetModule(
      using arena: Arena
    ): Attribute =
      Attribute(hwInnerRefAttrGetModule(arena, attr.segment))
    inline def innerRefAttrGetName(
      using arena: Arena
    ): Attribute =
      Attribute(hwInnerRefAttrGetName(arena, attr.segment))
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
  extension (attr: Attribute)
    inline def innerSymAttrGetSymName(
      using arena: Arena
    ): Attribute =
      Attribute(hwInnerSymAttrGetSymName(arena, attr.segment))
  inline def outputFileGetFileName(
    outputFile:  Attribute
  )(
    using arena: Arena
  ): Attribute =
    Attribute(hwOutputFileGetFileName(arena, outputFile.segment))
  inline def outputFileGetFromFileName(
    text:                Attribute,
    excludeFromFileList: Boolean,
    includeReplicatedOp: Boolean
  )(
    using arena:         Arena
  ): Attribute =
    Attribute(hwOutputFileGetFromFileName(arena, text.segment, excludeFromFileList, includeReplicatedOp))
  def paramDeclAttrGet(
    name:        String,
    tpe:         Type,
    value:       Attribute
  )(
    using arena: Arena
  ) =
    Attribute(hwParamDeclAttrGet(arena, name.toStringRef.segment, tpe.segment, value.segment))
  def paramDeclAttrGetName(
    decl:        Attribute
  )(
    using arena: Arena
  ): String = StringRef(hwParamDeclAttrGetName(arena, decl.segment)).toScalaString
  def paramDeclAttrGetType(
    decl:        Attribute
  )(
    using arena: Arena
  ): Type = Type(hwParamDeclAttrGetType(arena, decl.segment))
  def paramDeclAttrGetValue(
    decl:        Attribute
  )(
    using arena: Arena
  ): Attribute = Attribute(hwParamDeclAttrGetValue(arena, decl.segment))
  def paramDeclRefAttrGet(
    cName:       String
  )(
    using arena: Arena,
    context:     Context
  ): Attribute = Attribute(hwParamDeclRefAttrGet(arena, context.segment, cName.toStringRef.segment))
  def paramDeclRefAttrGetName(
    decl:        Attribute
  )(
    using arena: Arena
  ): String = StringRef(hwParamDeclRefAttrGetName(arena, decl.segment)).toScalaString
  def paramDeclRefAttrGetType(
    decl:        Attribute
  )(
    using arena: Arena
  ): Type = Type(hwParamDeclRefAttrGetType(arena, decl.segment))
  def paramVerbatimAttrGet(
    text:        Attribute
  )(
    using arena: Arena
  ): Attribute = Attribute(hwParamVerbatimAttrGet(arena, text.segment))
end given
