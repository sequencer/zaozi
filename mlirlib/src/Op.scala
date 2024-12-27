// SPDX-License-Identifier: Apache-2.0
package org.llvm.mlir.scalalib

import java.lang.foreign.Arena

trait Op(
  using arena: Arena,
  context: Context):
  val name:                     String
  val parent:                   Block
  // Location of this circuit
  val location:                 Location
  // Types and Location for each blocks in each region
  val regionBlockTypeLocations: Seq[Seq[(Seq[Type], Seq[Location])]]
  val namedAttributes:          Seq[NamedAttribute]
  val operands:                 Seq[Value]
  val resultsTypes:             Option[Seq[Type]]
  val inferredResultsTypes:     Option[Int]
  require(
    Seq(resultsTypes, inferredResultsTypes).count(_.isDefined) <= 1,
    s"Either resultsTypes: $resultsTypes or inferredResultsTypes: $inferredResultsTypes should be defined."
  )
  val regions:   Seq[Region] = regionBlockTypeLocations.map(blocks =>
    val region = summon[RegionApi].createRegion
    blocks.foreach(block =>
      val (tpe, loc) = block
      region.appendOwnedBlock(summon[BlockApi].createBlock(tpe, loc))
    )
    region
  )
  val operation: Operation   =
    val state = name.toOperationState(location)
    state.addAttributes(namedAttributes)
    state.addOperands(operands)
    inferredResultsTypes.foreach(_ => state.enableResultTypeInference())
    resultsTypes.foreach(resultsTypes => state.addResults(resultsTypes))
    state.addOwnedRegions(regions)
    state.toOperation
  val results:   Seq[Value]  = Seq.tabulate(inferredResultsTypes.getOrElse(resultsTypes.size))(operation.getResult)
  def region(idx: Int): Region = regions(idx)