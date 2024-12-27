// SPDX-License-Identifier: Apache-2.0
package org.llvm.circt.scalalib

import org.llvm.mlir.scalalib.{*, given}

import java.lang.foreign.Arena

object firrtl:
  def circuit(
    module:            org.llvm.mlir.scalalib.Module,
    circuitName:       String,
    rawAnnotationJson: String
  )(
    using arena:       Arena,
    context:           Context
  ): Circuit = new Circuit(
    module,
    circuitName,
    rawAnnotationJson
  )
  def module() = ???

class Circuit(
  val module:            org.llvm.mlir.scalalib.Module,
  val circuitName:       String,
  val rawAnnotationJson: String
)(
  using arena:           Arena,
  context:               Context)
    extends Op:
  val name:                     String                               = "firrtl.circuit"
  val parent:                   Block                                = module.getBody
  val location:                 Location                             = summon[LocationApi].unknownLocation
  val regionBlockTypeLocations: Seq[Seq[(Seq[Type], Seq[Location])]] =
    Seq(
      Seq(
        (Seq.empty, Seq.empty)
      )
    )
  val namedAttributes:          Seq[NamedAttribute]                  = Seq(
    "name".toIdentifier.toNamedAttribute(circuitName.toStringAttribute),
    "rawAnnotations".toIdentifier.toNamedAttribute(rawAnnotationJson.importAnnotationsFromJSONRaw),
    "annotations".toIdentifier.toNamedAttribute(Seq.empty[Attribute].toAttributeArrayAttribute)
  )
  val operands:                 Seq[Value]                           = Seq.empty
  val resultsTypes:             Option[Seq[Type]]                    = None
  val inferredResultsTypes:     Option[Int]                          = None

class Module(
  circuit:      Circuit,
  val location: Location,
  interface:    Seq[FirrtlBundleField]
)(
  using arena:  Arena,
  context:      Context)
    extends Op:
  override val name:                     String                               = "firrtl.module"
  override val parent:                   Block                                = circuit.region(0).block(0)
  override val regionBlockTypeLocations: Seq[Seq[(Seq[Type], Seq[Location])]] =
    ???
  override val namedAttributes:          Seq[NamedAttribute]                  = Seq(
    "sym_name".toIdentifier.toNamedAttribute("".toStringAttribute),
    "sym_visibility".toIdentifier.toNamedAttribute("".toStringAttribute),
    "convention".toIdentifier.toNamedAttribute("".toStringAttribute),
    "annotations".toIdentifier.toNamedAttribute("".toStringAttribute),
    "portDirections".toIdentifier.toNamedAttribute("".toStringAttribute),
    "portNames".toIdentifier.toNamedAttribute("".toStringAttribute),
    "portTypes".toIdentifier.toNamedAttribute("".toStringAttribute),
    "portAnnotations".toIdentifier.toNamedAttribute("".toStringAttribute),
    "portSymbols".toIdentifier.toNamedAttribute("".toStringAttribute),
    "portLocations".toIdentifier.toNamedAttribute("".toStringAttribute)
  )
  override val operands:                 Seq[Value]                           = ???
  override val resultsTypes:             Option[Seq[Type]]                    = ???
  override val inferredResultsTypes:     Option[Int]                          = ???
