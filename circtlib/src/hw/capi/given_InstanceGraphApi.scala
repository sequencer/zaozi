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

given InstanceGraphApi with
  extension (hwInstanceGraph:     HWInstanceGraph)
    inline def destroy: Unit = hwInstanceGraphDestroy(hwInstanceGraph.segment)
    inline def getTopLevelNode(
      using arena: Arena
    ): HWInstanceGraphNode = HWInstanceGraphNode(hwInstanceGraphGetTopLevelNode(arena, hwInstanceGraph.segment))
    inline def forEachNode(
      callback:    HWInstanceGraphNode => Unit
    )(
      using arena: Arena
    ): Unit =
      hwInstanceGraphForEachNode(
        hwInstanceGraph.segment,
        callback.toHWInstanceGraphNodeCallback.segment,
        MemorySegment.NULL
      )
  extension (operation:           Operation)
    inline def instanceGraphGet(
    )(
      using arena: Arena
    ): HWInstanceGraph = HWInstanceGraph(hwInstanceGraphGet(arena, operation.segment))
  extension (hwInstanceGraphNode: HWInstanceGraphNode)
    inline def equal(that: HWInstanceGraphNode): Boolean =
      hwInstanceGraphNodeEqual(hwInstanceGraphNode.segment, that.segment)
    inline def getModule(
      using arena: Arena
    ): Module = new Module(hwInstanceGraphNodeGetModule(arena, hwInstanceGraphNode.segment))
    inline def getModuleOp(
      using arena: Arena
    ): Operation = Operation(hwInstanceGraphNodeGetModuleOp(arena, hwInstanceGraphNode.segment))
end given
