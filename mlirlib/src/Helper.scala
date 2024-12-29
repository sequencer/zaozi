// SPDX-License-Identifier: Apache-2.0
package org.llvm.mlir.scalalib

import org.llvm.mlir.CAPI

import java.lang.foreign.{Arena, MemorySegment}
import scala.compiletime.summonFrom

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
          summonFrom:
            case hasSeg:    HasSegment[E]      =>
              buffer.asSlice(sizeOfT * i, sizeOfT).copyFrom(x.segment)
            case hasNative: EnumHasToNative[E] =>
              buffer.setAtIndex(CAPI.C_INT, i, x.toNative)
        buffer
      else MemorySegment.NULL
end given


inline def op(
               name:                     String,
               location:                 Location,
               regionBlockTypeLocations: Seq[Seq[(Seq[Type], Seq[Location])]] = Seq.empty,
               namedAttributes:          Seq[NamedAttribute] = Seq.empty,
               operands:                 Seq[Value] = Seq.empty,
               resultsTypes:             Option[Seq[Type]] = None,
               inferredResultsTypes:     Option[Int] = None
             )(
               using arena:              Arena,
               context:                  Context
             ) =
  val operationState = summon[OperationStateApi].operationStateGet(name, location)
  operationState.addOwnedRegions(
    regionBlockTypeLocations.map(blocks =>
      val region = summon[RegionApi].regionCreate
      blocks.foreach(block =>
        val (tpe: Seq[Type], loc: Seq[Location]) = block
        region.appendOwnedBlock(summon[BlockApi].blockCreate(tpe, loc))
      )
      region
    )
  )
  operationState.addAttributes(namedAttributes)
  operationState.addOperands(operands)
  inferredResultsTypes.foreach(_ => operationState.enableResultTypeInference())
  resultsTypes.foreach(resultsTypes => operationState.addResults(resultsTypes))
  summon[OperationApi].operationCreate(operationState)
