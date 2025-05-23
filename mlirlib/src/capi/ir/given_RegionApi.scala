// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.ir

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{
  mlirRegionAppendOwnedBlock,
  mlirRegionCreate,
  mlirRegionDestroy,
  mlirRegionGetFirstBlock,
  mlirRegionGetNextInOperation,
  mlirRegionInsertOwnedBlock,
  mlirRegionInsertOwnedBlockAfter,
  mlirRegionInsertOwnedBlockBefore
}

import java.lang.foreign.{Arena, MemorySegment}

given RegionApi with
  inline def regionCreate(
    using arena: Arena
  ): Region =
    Region(mlirRegionCreate(arena))

  extension (region: Region)
    inline def getFirstBlock(
      using arena: Arena
    ): Block = Block(mlirRegionGetFirstBlock(arena, region.segment))
    inline def getNextInOperation(
      using arena: Arena
    ): Region = Region(mlirRegionGetNextInOperation(arena, region.segment))
    inline def destroy(
    )(
      using arena: Arena
    ): Unit = mlirRegionDestroy(region.segment)
    inline def appendOwnedBlock(block: Block):                         Unit          =
      mlirRegionAppendOwnedBlock(region.segment, block.segment)
    inline def insertOwnedBlock(pos: Long, block: Block):              Unit          =
      mlirRegionInsertOwnedBlock(region.segment, pos, block.segment)
    inline def insertOwnedBlockAfter(reference: Block, block: Block):  Unit          =
      mlirRegionInsertOwnedBlockAfter(region.segment, reference.segment, block.segment)
    inline def insertOwnedBlockBefore(reference: Block, block: Block): Unit          =
      mlirRegionInsertOwnedBlockBefore(region.segment, reference.segment, block.segment)
    inline def segment:                                                MemorySegment = region._segment
    inline def sizeOf:                                                 Int           = MlirRegion.sizeof().toInt

end given
