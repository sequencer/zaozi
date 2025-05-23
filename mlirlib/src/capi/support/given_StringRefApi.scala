// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.support

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.mlirStringRefCreateFromCString

import java.lang.foreign.{Arena, MemorySegment}

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

  extension (bytes: Array[Byte])
    inline def toStringRef(
      using arena: Arena
    ): StringRef =
      val buffer    = arena.allocate(bytes.length)
      buffer.copyFrom(MemorySegment.ofArray(bytes))
      StringRef(mlirStringRefCreateFromCString(arena, buffer))
      val stringRef = MlirStringRef.allocate(arena)
      MlirStringRef.data$set(stringRef, buffer)
      MlirStringRef.length$set(stringRef, bytes.length)
      StringRef(stringRef)
end given

given StringCallbackApi with
  extension (stringCallBack: String => Unit)
    inline def stringToStringCallback(
      using arena: Arena
    ): StringCallback =
      StringCallback(
        MlirStringCallback.allocate(
          (message: MemorySegment, userData: MemorySegment) => stringCallBack(StringRef(message).toScalaString),
          arena
        )
      )
  extension (bytesCallBack:  Array[Byte] => Unit)
    inline def bytesToStringCallback(
      using arena: Arena
    ): StringCallback =
      StringCallback(
        MlirStringCallback.allocate(
          (message: MemorySegment, userData: MemorySegment) => bytesCallBack(StringRef(message).toBytes),
          arena
        )
      )
  extension (stringCallBack: StringCallback) inline def segment: MemorySegment = stringCallBack._segment
end given
