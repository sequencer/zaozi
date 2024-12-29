// SPDX-License-Identifier: Apache-2.0
package org.llvm.mlir.scalalib

import org.llvm.mlir.CAPI

import java.lang.foreign.{Arena, MemorySegment}
import scala.compiletime.summonFrom

trait Op(
  val name:                     String,
  val parent:                   Block,
  val location:                 Location,
  val regionBlockTypeLocations: Seq[Seq[(Seq[Type], Seq[Location])]],
  val namedAttributes:          Seq[NamedAttribute],
  val operands:                 Seq[Value],
  val resultsTypes:             Option[Seq[Type]],
  val inferredResultsTypes:     Option[Int]
)(
  using arena:                  Arena,
  context: Context):

  require(
    Seq(resultsTypes, inferredResultsTypes).count(_.isDefined) <= 1,
    s"Either resultsTypes: $resultsTypes or inferredResultsTypes: $inferredResultsTypes should be defined."
  )
  val regions:   Seq[Region] = regionBlockTypeLocations.map(blocks =>
    val region = summon[RegionApi].regionCreate
    blocks.foreach(block =>
      val (tpe: Seq[Type], loc: Seq[Location]) = block
      region.appendOwnedBlock(summon[BlockApi].blockCreate(tpe, loc))
    )
    region
  )
  val operation: Operation   =
    val state = summon[OperationStateApi].operationStateGet(name, location)
    state.addAttributes(namedAttributes)
    state.addOperands(operands)
    inferredResultsTypes.foreach(_ => state.enableResultTypeInference())
    resultsTypes.foreach(resultsTypes => state.addResults(resultsTypes))
    state.addOwnedRegions(regions)
    summon[OperationApi].operationCreate(state)
  val results:   Seq[Value]  =
    Seq.tabulate(inferredResultsTypes.getOrElse(resultsTypes.size))(i => operation.getResult(i))
  def region(idx: Int): Region = regions(idx)

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
