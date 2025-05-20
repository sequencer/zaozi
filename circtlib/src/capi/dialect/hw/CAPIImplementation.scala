// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.dialect.hw

import java.lang.foreign.{Arena, MemorySegment}

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
