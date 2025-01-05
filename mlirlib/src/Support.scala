// SPDX-License-Identifier: Apache-2.0
package org.llvm.mlir.scalalib

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.*

import java.lang.foreign.{Arena, MemorySegment}

given [E]: ToMlirArray[E] with
  extension (xs: Seq[E])
    inline def toMlirArray(
      using arena: Arena,
      api:         HasSizeOf[E] & (HasSegment[E] | EnumHasToNative[E])
    ): MemorySegment =
      if (xs.nonEmpty)
        val sizeOfT: Int = xs.head.sizeOf
        val buffer = arena.allocate(sizeOfT * xs.length)
        xs.zipWithIndex.foreach: (x, i) =>
          scala.compiletime.summonFrom:
            case hasSeg:    HasSegment[E]      =>
              buffer.asSlice(sizeOfT * i, sizeOfT).copyFrom(x.segment)
            case hasNative: EnumHasToNative[E] =>
              buffer.setAtIndex(CAPI.C_INT, i, x.toNative)
        buffer
      else MemorySegment.NULL
end given

given StringRefApi with
  extension (stringRef: StringRef)
    inline def segment:       MemorySegment = stringRef._segment
    inline def sizeOf:        Int           = MlirStringRef.sizeof().toInt
    inline def toBytes:       Array[Byte]   =
      MlirStringRef
        .data$get(stringRef.segment)
        .asSlice(0, MlirStringRef.length$get(stringRef.segment))
        .toArray(java.lang.foreign.ValueLayout.JAVA_BYTE)
    inline def toScalaString: String        = String(toBytes)
  extension (string:    String)
    inline def toStringRef(
      using arena: Arena
    ): StringRef =
      val bytes  = string.getBytes()
      val buffer = arena.allocate(bytes.length + 1)
      buffer.copyFrom(MemorySegment.ofArray(bytes))
      StringRef(mlirStringRefCreateFromCString(arena, buffer))
end given

given LogicalResultApi with
  extension (logicalResult: LogicalResult)
    inline def segment: MemorySegment = logicalResult._segment
    inline def sizeOf:  Int           = MlirLogicalResult.sizeof().toInt
end given

given LlvmThreadPoolApi with
  inline def llvmThreadPoolCreate(
  )(
    using arena: Arena
  ): LlvmThreadPool = LlvmThreadPool(mlirLlvmThreadPoolCreate(arena))
  extension (llvmThreadPool: LlvmThreadPool)
    inline def destroy(): Unit          = mlirLlvmThreadPoolDestroy(llvmThreadPool.segment)
    inline def segment:   MemorySegment = llvmThreadPool._segment
    inline def sizeOf:    Int           = MlirLlvmThreadPool.sizeof().toInt
end given

given TypeIDApi with
  extension (typeID: TypeID)
    inline def segment: MemorySegment = typeID._segment
    inline def sizeOf:  Int           = MlirTypeID.sizeof().toInt
end given

given TypeIDAllocatorApi with
  extension (typeIDAllocator: TypeIDAllocator)
    inline def segment: MemorySegment = typeIDAllocator._segment
    inline def sizeOf:  Int           = MlirTypeIDAllocator.sizeof().toInt
end given
