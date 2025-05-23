// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.ir

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.{
  mlirLocationCallSiteGet,
  mlirLocationFileLineColGet,
  mlirLocationFromAttribute,
  mlirLocationFusedGet,
  mlirLocationGetAttribute,
  mlirLocationGetContext,
  mlirLocationNameGet,
  mlirLocationPrint,
  mlirLocationUnknownGet
}
import org.llvm.mlir.scalalib.capi.support.{*, given}

import java.lang.foreign.{Arena, MemorySegment}

given LocationApi with
  inline def locationFromAttribute(
    attribute: Attribute
  )(arena:     Arena
  ): Location = Location(mlirLocationFromAttribute(arena, attribute.segment))
  inline def locationFileLineColGet(
    filename:    String,
    line:        Int,
    col:         Int
  )(
    using arena: Arena,
    context:     Context
  ): Location =
    Location(mlirLocationFileLineColGet(arena, context.segment, filename.toStringRef.segment, line, col))
  inline def locationCallSiteGet(
    callee:      Location,
    caller:      Location
  )(
    using arena: Arena,
    context:     Context
  ): Location = Location(mlirLocationCallSiteGet(arena, callee.segment, caller.segment))
  inline def locationFusedGet(
    locations:   Seq[Location],
    metadata:    Attribute
  )(
    using arena: Arena,
    context:     Context
  ): Location =
    Location(mlirLocationFusedGet(arena, context.segment, locations.size, locations.toMlirArray, metadata.segment))
  inline def locationNameGet(
    name:        String,
    childLoc:    Location
  )(
    using arena: Arena,
    context:     Context
  ): Location = Location(mlirLocationNameGet(arena, context.segment, name.toStringRef.segment, childLoc.segment))
  inline def locationUnknownGet(
    using arena: Arena,
    context:     Context
  ): Location = Location(mlirLocationUnknownGet(arena, context.segment))
  extension (location: Location)
    inline def getAttribute(
      using arena: Arena
    ): Attribute =
      Attribute(mlirLocationGetAttribute(arena, location.segment))
    inline def getContext(
      using arena: Arena
    ): Context = Context(mlirLocationGetContext(arena, location.segment))
    inline def print(
      callback:    StringCallback
    )(
      using arena: Arena
    ): Unit =
      // The opaque data is meaningless here since Scala supports function currying
      mlirLocationPrint(location.segment, callback.segment, MemorySegment.NULL)
    inline def segment: MemorySegment = location._segment
    inline def sizeOf:  Int           = MlirLocation.sizeof().toInt
end given
