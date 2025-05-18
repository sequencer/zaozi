// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Yuhang Zeng <unlsycn@unlsycn.com>
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

given HWModulePortApi with
  extension (ref: HWModulePort)
    inline def segment: MemorySegment = ref._segment
    inline def sizeOf:  Int           = org.llvm.circt.HWModulePort.sizeof().toInt
end given

given HWStructFieldInfoApi with
  extension (ref: HWStructFieldInfo)
    inline def segment: MemorySegment = ref._segment
    inline def sizeOf:  Int           = org.llvm.circt.HWStructFieldInfo.sizeof().toInt
end given

given HWInstanceGraphNodeCallbackApi with
  extension (hwInstanceGraphNodeCallback: HWInstanceGraphNode => Unit)
    inline def toHWInstanceGraphNodeCallback(
      using arena: Arena
    ): InstanceGraphNodeCallback =
      InstanceGraphNodeCallback(
        org.llvm.circt.HWInstanceGraphNodeCallback.allocate(
          (hwInstanceGraphNode: MemorySegment, userData: MemorySegment) =>
            hwInstanceGraphNodeCallback(HWInstanceGraphNode(hwInstanceGraphNode)),
          arena
        )
      )
  extension (hwInstanceGraphNodeCallback: InstanceGraphNodeCallback)
    inline def segment: MemorySegment = hwInstanceGraphNodeCallback._segment
end given

given HWInstanceGraphApi with
  extension (ref: HWInstanceGraph)
    inline def segment: MemorySegment = ref._segment
    inline def sizeOf:  Int           = org.llvm.circt.HWInstanceGraph.sizeof().toInt
end given

given HWInstanceGraphNodeApi with
  extension (ref: HWInstanceGraphNode)
    inline def segment: MemorySegment = ref._segment
    inline def sizeOf:  Int           = org.llvm.circt.HWInstanceGraphNode.sizeof().toInt
end given
