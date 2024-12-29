// SPDX-License-Identifier: Apache-2.0
package org.llvm.circt.scalalib.operator

import org.llvm.circt.scalalib.{*, given}
import org.llvm.mlir.scalalib
import org.llvm.mlir.scalalib.{Module as MlirModule, *, given}

import java.lang.foreign.Arena

class Circuit(val operation: Operation):
  inline def block(
    using Arena
  ): Block = operation.getFirstRegion().getFirstBlock()
  inline def appendToModule(
  )(
    using arena: Arena,
    module:      MlirModule
  ): Unit = module.getBody.appendOwnedOperation(operation)

inline def circuit(
  circuitName: String
)(
  using arena: Arena,
  context:     Context,
  module:      MlirModule
) =
  Circuit(
    op(
      name = "firrtl.circuit",
      location = summon[LocationApi].locationUnknownGet,
      regionBlockTypeLocations = Seq(
        Seq(
          (Seq.empty, Seq.empty)
        )
      ),
      namedAttributes = Seq(
        summon[NamedAttributeApi].namedAttributeGet("name".identifierGet, circuitName.stringAttrGet)
      )
    )
  )

class Module(val operation: Operation):
  inline def block(
    using Arena
  ): Block = operation.getFirstRegion().getFirstBlock()
  inline def appendToCircuit(
  )(
    using arena: Arena,
    circuit:     Circuit
  ): Unit = circuit.block.appendOwnedOperation(operation)
  inline def addOperation(
    operation: Operation
  )(
    using Arena
  ): Unit = block.appendOwnedOperation(operation)
  inline def getIO(
    idx: Long
  )(
    using Arena
  ): Value = block.getArgument(idx)

inline def module(
  name:        String,
  location:    Location,
  interface:   Seq[(FirrtlBundleField, Location)]
)(
  using arena: Arena,
  context:     Context,
  circuit:     Circuit
) = new Module(
  op(
    name = "firrtl.module",
    location = location,
    regionBlockTypeLocations = Seq(
      Seq(
        (interface.map(_._1.getType()), interface.map(_._2))
      )
    ),
    namedAttributes =
      val namedAttributeApi = summon[NamedAttributeApi]
      Seq(
        namedAttributeApi.namedAttributeGet(
          "sym_name".identifierGet,
          name.stringAttrGet
        ),
        namedAttributeApi.namedAttributeGet(
          "portDirections".identifierGet,
          interface
            .map:
              case (bf, _) =>
                if (bf.getIsFlip()) FirrtlDirection.In else FirrtlDirection.Out
            .attrGetPortDirs
        ),
        namedAttributeApi.namedAttributeGet(
          "portLocations".identifierGet,
          interface.map(_._2.getAttribute).arrayAttrGet
        ),
        namedAttributeApi.namedAttributeGet(
          "portAnnotations".identifierGet,
          Seq().arrayAttrGet
        ),
        namedAttributeApi.namedAttributeGet(
          "portSymbols".identifierGet,
          Seq().arrayAttrGet
        ),
        namedAttributeApi.namedAttributeGet(
          "portNames".identifierGet,
          interface.map(_._1.getName().stringAttrGet).arrayAttrGet
        ),
        namedAttributeApi.namedAttributeGet(
          "portTypes".identifierGet,
          interface.map(_._1.getType().typeAttrGet).arrayAttrGet
        )
      )
  )
)

class Connect(val operation: Operation)
inline def connect(
  src:         Value,
  dst:         Value,
  location:    Location
)(
  using arena: Arena,
  context:     Context,
  module:      Module
) =
  val connect = Connect(
    op(
      name = "firrtl.connect",
      location = location,
      operands = Seq(dst, src)
    )
  )
  module.addOperation(connect.operation)
  connect
