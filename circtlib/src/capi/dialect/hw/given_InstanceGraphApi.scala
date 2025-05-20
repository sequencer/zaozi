// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.dialect.hw

import org.llvm.circt.CAPI.{
  hwInstanceGraphDestroy,
  hwInstanceGraphForEachNode,
  hwInstanceGraphGet,
  hwInstanceGraphGetTopLevelNode,
  hwInstanceGraphNodeEqual,
  hwInstanceGraphNodeGetModule,
  hwInstanceGraphNodeGetModuleOp
}
import org.llvm.mlir.scalalib.given
import org.llvm.mlir.scalalib.{Module, Operation}

import java.lang.foreign.{Arena, MemorySegment}

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
