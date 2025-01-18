// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.firrtl.operation

import org.llvm.circt.scalalib.firrtl.capi.{FirrtlBundleField, FirrtlConvention, FirrtlLayerConvention}
import org.llvm.mlir.scalalib.{Block, Context, HasOperation, Location, Module as MlirModule, Operation, Value, given}

import java.lang.foreign.Arena

class Circuit(val _operation: Operation)
trait CircuitApi extends HasOperation[Circuit]:
  inline def op(
    circuitName: String
  )(
    using arena: Arena,
    context:     Context
  ): Circuit

  extension (c: Circuit)
    inline def block(
      using Arena
    ): Block
    inline def appendToModule(
    )(
      using arena: Arena,
      module:      MlirModule
    ): Unit
end CircuitApi

class Class(val _operation: Operation)
class ExtClass(val _operation: Operation)
class ExtModule(val _operation: Operation)
trait ExtModuleApi extends HasOperation[ExtModule]:
end ExtModuleApi

class IntModule(val _operation: Operation)
class MemModule(val _operation: Operation)
class Module(val _operation: Operation)
trait ModuleApi extends HasOperation[Module]:
  inline def op(
    name:             String,
    location:         Location,
    firrtlConvention: FirrtlConvention,
    interface:        Seq[(FirrtlBundleField, Location)],
    layers:           Seq[Seq[String]]
  )(
    using arena:      Arena,
    context:          Context
  ): Module

  extension (m: Module)
    inline def block(
      using Arena
    ): Block
    inline def appendToCircuit(
    )(
      using arena: Arena,
      circuit:     Circuit
    ): Unit
    inline def getIO(
      idx: Long
    )(
      using Arena
    ): Value
end ModuleApi

class Formal(val _operation: Operation)
class Layer(val _operation: Operation)
trait LayerApi extends HasOperation[Layer]:
  inline def op(
    name:            String,
    location:        Location,
    layerConvention: FirrtlLayerConvention
  )(
    using arena:     Arena,
    context:         Context
  ): Layer
end LayerApi
class OptionCase(val _operation: Operation)
class Option(val _operation: Operation)
