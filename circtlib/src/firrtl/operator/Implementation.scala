// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.firrtl.operation

import org.llvm.circt.scalalib.firrtl.capi.{
  FirrtlBundleField,
  FirrtlConvention,
  FirrtlDirection,
  FirrtlLayerConvention,
  FirrtlNameKind,
  given
}
import org.llvm.mlir.scalalib.{
  Block,
  Context,
  Location,
  LocationApi,
  Module as MlirModule,
  NamedAttributeApi,
  Operation,
  OperationApi,
  Type,
  Value,
  given
}

import java.lang.foreign.Arena

// Structure
given CircuitApi with
  inline def op(
    circuitName: String
  )(
    using arena: Arena,
    context:     Context
  ): Circuit = Circuit(
    summon[OperationApi].operationCreate(
      name = "firrtl.circuit",
      location = summon[LocationApi].locationUnknownGet,
      regionBlockTypeLocations = Seq(
        Seq(
          (Seq.empty, Seq.empty)
        )
      ),
      namedAttributes =
        val namedAttributeApi = summon[NamedAttributeApi]
        Seq(
          // ::mlir::StringAttr
          namedAttributeApi.namedAttributeGet("name".identifierGet, circuitName.stringAttrGet)
          // ::mlir::ArrayAttr
          // namedAttributeApi.namedAttributeGet("annotations".identifierGet, ???),
          // ::mlir::ArrayAttr
          // namedAttributeApi.namedAttributeGet("enable_layers".identifierGet, ???),
          // ::mlir::ArrayAttr
          // namedAttributeApi.namedAttributeGet("disable_layers".identifierGet, ???),
          // ::circt::firrtl::LayerSpecializationAttr
          // namedAttributeApi.namedAttributeGet("default_layer_specialization".identifierGet, ???),
          // ::mlir::ArrayAttr
          // namedAttributeApi.namedAttributeGet("select_inst_choice".identifierGet, ???),
        )
    )
  )
  extension (c:   Circuit)
    inline def block(
      using Arena
    ): Block = c.operation.getFirstRegion.getFirstBlock
    inline def appendToModule(
    )(
      using arena: Arena,
      module:      MlirModule
    ): Unit =
      module.getBody.appendOwnedOperation(c.operation)
  extension (ref: Circuit) def operation: Operation = ref._operation
end given
given ExtModuleApi with
  inline def op(
    name:             String,
    location:         Location,
    firrtlConvention: FirrtlConvention,
    interface:        Seq[(FirrtlBundleField, Location)]
  )(
    using Arena,
    Context
  ): ExtModule =
    new ExtModule(
      summon[OperationApi].operationCreate(
        name = "firrtl.extmodule",
        location = location,
        regionBlockTypeLocations = Seq(
          Seq(
            (interface.map(_._1.getType), interface.map(_._2))
          )
        ),
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::StringAttr
            namedAttributeApi.namedAttributeGet(
              "sym_name".identifierGet,
              name.stringAttrGet
            ),
            // ::mlir::StringAttr
            namedAttributeApi.namedAttributeGet(
              "defname".identifierGet,
              name.stringAttrGet
            ),
            // ::circt::firrtl::ConventionAttr
            namedAttributeApi.namedAttributeGet(
              "convention".identifierGet,
              firrtlConvention.toAttribute
            ),
            // ::mlir::DenseBoolArrayAttr
            namedAttributeApi.namedAttributeGet(
              "portDirections".identifierGet,
              interface
                .map:
                  case (bf, _) =>
                    if (bf.getIsFlip) FirrtlDirection.In else FirrtlDirection.Out
                .attrGetPortDirs
            ),
            // ::mlir::ArrayAttr
            namedAttributeApi.namedAttributeGet(
              "portLocations".identifierGet,
              interface.map(_._2.getAttribute).arrayAttrGet
            ),
            // ::mlir::ArrayAttr
            namedAttributeApi.namedAttributeGet(
              "portAnnotations".identifierGet,
              Seq.empty.arrayAttrGet
            ),
            // ::mlir::ArrayAttr
            namedAttributeApi.namedAttributeGet(
              "portSymbols".identifierGet,
              Seq.empty.arrayAttrGet
            ),
            // ::mlir::ArrayAttr
            namedAttributeApi.namedAttributeGet(
              "portNames".identifierGet,
              interface.map(_._1.getName.stringAttrGet).arrayAttrGet
            ),
            // ::mlir::ArrayAttr
            namedAttributeApi.namedAttributeGet(
              "portTypes".identifierGet,
              interface.map(_._1.getType.typeAttrGet).arrayAttrGet
            ),
            // ::mlir::ArrayAttr
            namedAttributeApi.namedAttributeGet(
              "annotations".identifierGet,
              Seq.empty.arrayAttrGet
            )
            // ::mlir::ArrayAttr
            // namedAttributeApi.namedAttributeGet(
            //   "layers".identifierGet, ???
            // ),
            // ::mlir::ArrayAttr
            // namedAttributeApi.namedAttributeGet(
            //   "internalPaths".identifierGet, ???
            // )
          )
      )
    )
  extension (ref: ExtModule) def operation: Operation = ref._operation
end given

given ModuleApi with
  inline def op(
    name:             String,
    location:         Location,
    firrtlConvention: FirrtlConvention,
    interface:        Seq[(FirrtlBundleField, Location)],
    layers:           Seq[Seq[String]]
  )(
    using arena:      Arena,
    context:          Context
  ): Module = new Module(
    summon[OperationApi].operationCreate(
      name = "firrtl.module",
      location = location,
      regionBlockTypeLocations = Seq(
        Seq(
          (interface.map(_._1.getType), interface.map(_._2))
        )
      ),
      namedAttributes =
        val namedAttributeApi = summon[NamedAttributeApi]
        Seq(
          // ::mlir::StringAttr
          namedAttributeApi.namedAttributeGet(
            "sym_name".identifierGet,
            name.stringAttrGet
          ),
          // ::circt::firrtl::ConventionAttr
          namedAttributeApi.namedAttributeGet("convention".identifierGet, firrtlConvention.toAttribute),
          // ::mlir::DenseBoolArrayAttr
          namedAttributeApi.namedAttributeGet(
            "portDirections".identifierGet,
            interface
              .map:
                case (bf, _) =>
                  if (bf.getIsFlip) FirrtlDirection.In else FirrtlDirection.Out
              .attrGetPortDirs
          ),
          // ::mlir::ArrayAttr
          namedAttributeApi.namedAttributeGet(
            "portLocations".identifierGet,
            interface.map(_._2.getAttribute).arrayAttrGet
          ),
          // ::mlir::ArrayAttr
          namedAttributeApi.namedAttributeGet(
            "portAnnotations".identifierGet,
            Seq().arrayAttrGet
          ),
          // ::mlir::ArrayAttr
          namedAttributeApi.namedAttributeGet(
            "portSymbols".identifierGet,
            Seq().arrayAttrGet
          ),
          // ::mlir::ArrayAttr
          namedAttributeApi.namedAttributeGet(
            "portNames".identifierGet,
            interface.map(_._1.getName.stringAttrGet).arrayAttrGet
          ),
          // ::mlir::ArrayAttr
          namedAttributeApi.namedAttributeGet(
            "portTypes".identifierGet,
            interface.map(_._1.getType.typeAttrGet).arrayAttrGet
          ),
          // ::mlir::ArrayAttr
          // namedAttributeApi.namedAttributeGet("annotations".identifierGet, ???),
          // ::mlir::ArrayAttr
          namedAttributeApi.namedAttributeGet(
            "layers".identifierGet,
            layers
              .map(path => path.reverse.last.symbolRefAttrGet(path.drop(1).map(_.flatSymbolRefAttrGet)))
              .arrayAttrGet
          )
        )
    )
  )
  extension (ref: Module)
    inline def block(
      using Arena
    ): Block = operation.getFirstRegion.getFirstBlock

    inline def getIO(
      idx: Long
    )(
      using Arena
    ): Value = block.getArgument(idx)

    inline def appendToCircuit(
    )(
      using arena: Arena,
      circuit:     Circuit
    ): Unit =
      circuit.block.appendOwnedOperation(ref.operation)

    inline def operation: Operation = ref._operation
end given

given LayerApi with
  inline def op(
    name:            String,
    location:        Location,
    layerConvention: FirrtlLayerConvention
  )(
    using arena:     Arena,
    context:         Context
  ): Layer =
    Layer(
      summon[OperationApi].operationCreate(
        name = "firrtl.layer",
        location = location,
        regionBlockTypeLocations = Seq(
          Seq(
            (Seq.empty, Seq.empty)
          )
        ),
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::StringAttr
            namedAttributeApi.namedAttributeGet(
              "sym_name".identifierGet,
              name.stringAttrGet
            ),
            // ::circt::firrtl::LayerConventionAttr
            namedAttributeApi.namedAttributeGet(
              "convention".identifierGet,
              layerConvention.toAttribute
            )
          )
      )
    )
  extension (ref: Layer)
    inline def block(
      using Arena
    ): Block = operation.getFirstRegion.getFirstBlock
    inline def operation: Operation = ref._operation
end given
// Declarations
given InstanceApi with
  inline def op(
    moduleName:   String,
    instanceName: String,
    nameKind:     FirrtlNameKind,
    location:     Location,
    interface:    Seq[FirrtlBundleField]
  )(
    using arena:  Arena,
    context:      Context
  ): Instance =
    new Instance(
      summon[OperationApi].operationCreate(
        name = "firrtl.instance",
        location = location,
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::FlatSymbolRefAttr
            namedAttributeApi.namedAttributeGet("moduleName".identifierGet, moduleName.flatSymbolRefAttrGet),
            // ::mlir::StringAttr
            namedAttributeApi.namedAttributeGet("name".identifierGet, instanceName.stringAttrGet),
            // ::circt::firrtl::NameKindEnumAttr
            namedAttributeApi.namedAttributeGet("nameKind".identifierGet, nameKind.attrGetNameKind),
            // ::mlir::DenseBoolArrayAttr
            namedAttributeApi.namedAttributeGet(
              "portDirections".identifierGet,
              interface
                .map: bf =>
                  if (bf.getIsFlip) FirrtlDirection.In else FirrtlDirection.Out
                .attrGetPortDirs
            ),
            // ::mlir::ArrayAttr
            namedAttributeApi.namedAttributeGet(
              "portNames".identifierGet,
              interface.map(_.getName.stringAttrGet).arrayAttrGet
            ),
            // ::mlir::ArrayAttr
            namedAttributeApi.namedAttributeGet("annotations".identifierGet, Seq.empty.arrayAttrGet),
            // ::mlir::ArrayAttr
            namedAttributeApi.namedAttributeGet(
              "portAnnotations".identifierGet,
              interface.map(_ => Seq.empty.arrayAttrGet).arrayAttrGet
            ),
            // ::mlir::ArrayAttr
            namedAttributeApi.namedAttributeGet("layers".identifierGet, Seq.empty.arrayAttrGet)
            // ::mlir::UnitAttr
            // namedAttributeApi.namedAttributeGet("lowerToBind".identifierGet, ???),
            // ::circt::hw::InnerSymAttr
            // namedAttributeApi.namedAttributeGet("inner_sym".identifierGet, ???)
          )
        ,
        resultsTypes = Some(interface.map(_.getType))
      )
    )
  extension (ref: Instance) def operation: Operation = ref._operation
end given

given NodeApi with
  inline def op(
    name:        String,
    location:    Location,
    nameKind:    FirrtlNameKind,
    input:       Value
  )(
    using arena: Arena,
    context:     Context
  ): Node =
    Node(
      summon[OperationApi].operationCreate(
        name = "firrtl.node",
        location = location,
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::StringAttr
            namedAttributeApi.namedAttributeGet("name".identifierGet, name.stringAttrGet),
            // ::circt::firrtl::NameKindEnumAttr
            namedAttributeApi.namedAttributeGet("nameKind".identifierGet, nameKind.attrGetNameKind),
            // ::mlir::ArrayAttr
            namedAttributeApi.namedAttributeGet("annotations".identifierGet, Seq.empty.arrayAttrGet)
            // ::circt::hw::InnerSymAttr
            // namedAttributeApi.namedAttributeGet("inner_sym".identifierGet, ???),
            // ::mlir::UnitAttr
            // namedAttributeApi.namedAttributeGet("forceable".identifierGet, ???)
          )
        ,
        operands = Seq(input),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: Node) def operation: Operation = ref._operation
end given

given RegApi with
  inline def op(
    name:        String,
    location:    Location,
    nameKind:    FirrtlNameKind,
    tpe:         Type,
    clock:       Value
  )(
    using arena: Arena,
    context:     Context
  ): Reg = Reg(
    summon[OperationApi].operationCreate(
      name = "firrtl.reg",
      location = location,
      namedAttributes =
        val namedAttributeApi = summon[NamedAttributeApi]
        Seq(
          // ::mlir::StringAttr
          namedAttributeApi.namedAttributeGet("name".identifierGet, name.stringAttrGet),
          // ::circt::firrtl::NameKindEnumAttr
          namedAttributeApi.namedAttributeGet("nameKind".identifierGet, nameKind.attrGetNameKind),
          // ::mlir::ArrayAttr
          namedAttributeApi.namedAttributeGet("annotations".identifierGet, Seq.empty.arrayAttrGet)
          // ::circt::hw::InnerSymAttr
          // namedAttributeApi.namedAttributeGet("inner_sym".identifierGet, ???),
          // ::mlir::UnitAttr
          // namedAttributeApi.namedAttributeGet("forceable".identifierGet, ???)
        )
      ,
      operands = Seq(clock),
      resultsTypes = Some(Seq(tpe))
    )
  )
  extension (ref: Reg) def operation: Operation = ref._operation
end given
given RegResetApi with
  inline def op(
    name:        String,
    location:    Location,
    nameKind:    FirrtlNameKind,
    tpe:         Type,
    clock:       Value,
    reset:       Value,
    resetValue:  Value
  )(
    using arena: Arena,
    context:     Context
  ): RegReset = RegReset(
    summon[OperationApi].operationCreate(
      name = "firrtl.regreset",
      location = location,
      namedAttributes =
        val namedAttributeApi = summon[NamedAttributeApi]
        Seq(
          // ::mlir::StringAttr
          namedAttributeApi.namedAttributeGet("name".identifierGet, name.stringAttrGet),
          // ::circt::firrtl::NameKindEnumAttr
          namedAttributeApi.namedAttributeGet("nameKind".identifierGet, nameKind.attrGetNameKind),
          // ::mlir::ArrayAttr
          namedAttributeApi.namedAttributeGet("annotations".identifierGet, Seq.empty.arrayAttrGet)
          // ::circt::hw::InnerSymAttr
          // namedAttributeApi.namedAttributeGet("inner_sym".identifierGet, ???),
          // ::mlir::UnitAttr
          // namedAttributeApi.namedAttributeGet("forceable".identifierGet, ???)
        )
      ,
      operands = Seq(clock, reset, resetValue),
      resultsTypes = Some(Seq(tpe))
    )
  )
  extension (ref: RegReset) def operation: Operation = ref._operation
end given
given WireApi with
  def op(
    name:        String,
    location:    Location,
    nameKind:    FirrtlNameKind,
    tpe:         Type
  )(
    using arena: Arena,
    context:     Context
  ): Wire =
    Wire(
      summon[OperationApi].operationCreate(
        name = "firrtl.wire",
        location = location,
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::StringAttr
            namedAttributeApi.namedAttributeGet("name".identifierGet, name.stringAttrGet),
            // ::circt::firrtl::NameKindEnumAttr
            namedAttributeApi.namedAttributeGet("nameKind".identifierGet, nameKind.attrGetNameKind),
            // ::mlir::ArrayAttr
            namedAttributeApi.namedAttributeGet("annotations".identifierGet, Seq.empty.arrayAttrGet)
            // ::circt::hw::InnerSymAttr
            // namedAttributeApi.namedAttributeGet("inner_sym".identifierGet, ???),
            // ::mlir::UnitAttr
            // namedAttributeApi.namedAttributeGet("forceable".identifierGet, ???)
          )
        ,
        resultsTypes = Some(Seq(tpe))
      )
    )
  extension (ref: Wire)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)
end given

// Statements
given ConnectApi with
  inline def op(
    src:         Value,
    dst:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): Connect =
    Connect(
      summon[OperationApi].operationCreate(
        name = "firrtl.connect",
        location = location,
        operands = Seq(dst, src)
      )
    )
  extension (ref: Connect) def operation: Operation = ref._operation
end given

given LayerBlockApi with
  inline def op(
    layerPath:   Seq[String],
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): LayerBlock =
    LayerBlock(
      summon[OperationApi].operationCreate(
        name = "firrtl.layerblock",
        location = location,
        regionBlockTypeLocations = Seq(
          Seq((Seq.empty, Seq.empty))
        ),
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::SymbolRefAttr
            namedAttributeApi.namedAttributeGet(
              "layerName".identifierGet,
              layerPath.reverse.last.symbolRefAttrGet(layerPath.drop(1).map(_.flatSymbolRefAttrGet))
            )
          )
      )
    )
  extension (ref: LayerBlock)
    inline def block(
      using Arena
    ): Block = operation.getFirstRegion.getFirstBlock
    def operation: Operation = ref._operation
end given

given RefDefineApi with
  inline def op(
    dest:        Value,
    src:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): RefDefine =
    RefDefine(
      summon[OperationApi].operationCreate(
        name = "firrtl.ref.define",
        location = location,
        operands = Seq(dest, src)
      )
    )
  extension (ref: RefDefine) def operation: Operation = ref._operation
end given

given RefForceInitialApi with
  inline def op(
    predicate:   Value,
    dest:        Value,
    src:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): RefForceInitial =
    RefForceInitial(
      summon[OperationApi].operationCreate(
        name = "firrtl.ref.force_initial",
        location = location,
        operands = Seq(predicate, dest, src)
      )
    )

  extension (ref: RefForceInitial) def operation: Operation = ref._operation
end given

given RefForceApi with
  inline def op(
    clock:       Value,
    predicate:   Value,
    dest:        Value,
    src:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): RefForce =
    RefForce(
      summon[OperationApi].operationCreate(
        name = "firrtl.ref.force",
        location = location,
        operands = Seq(clock, predicate, dest, src)
      )
    )
  extension (ref: RefForce) def operation: Operation = ref._operation
end given

given RefReleaseInitialApi with
  inline def op(
    predicate:   Value,
    dest:        Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): RefReleaseInitial =
    RefReleaseInitial(
      summon[OperationApi].operationCreate(
        name = "firrtl.ref.release",
        location = location,
        operands = Seq(predicate, dest)
      )
    )

  extension (ref: RefReleaseInitial) def operation: Operation = ref._operation
end given

given RefReleaseApi with
  inline def op(
    clock:       Value,
    predicate:   Value,
    dest:        Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): RefRelease =
    RefRelease(
      summon[OperationApi].operationCreate(
        name = "firrtl.ref.release",
        location = location,
        operands = Seq(clock, predicate, dest)
      )
    )
  extension (ref: RefRelease) def operation: Operation = ref._operation
end given

given WhenApi with
  inline def op(
    cond:        Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): When =
    When(
      summon[OperationApi].operationCreate(
        name = "firrtl.when",
        location = location,
        operands = Seq(cond),
        regionBlockTypeLocations = Seq(
          // cond
          Seq((Seq.empty, Seq.empty)),
          // else
          Seq((Seq.empty, Seq.empty))
        )
      )
    )
  extension (ref: When)
    def operation: Operation = ref._operation
    def condBlock(
      using Arena
    ): Block = operation.getRegion(0).getFirstBlock
    def elseBlock(
      using Arena
    ): Block = operation.getRegion(1).getFirstBlock
end given
// Expression
given AddPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): AddPrim =
    AddPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.add",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: AddPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)
end given

given AndPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): AndPrim =
    AndPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.and",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: AndPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = operation.getResult(0)

end given

given AndRPrimApi with
  def op(
    input:       Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): AndRPrim = AndRPrim(
    summon[OperationApi].operationCreate(
      name = "firrtl.andr",
      location = location,
      operands = Seq(input),
      inferredResultsTypes = Some(1)
    )
  )
  extension (ref: AndRPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = operation.getResult(0)

end given

given AsAsyncResetPrimApi with
  def op(
    input:       Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): AsAsyncResetPrim =
    AsAsyncResetPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.asAsyncReset",
        location = location,
        operands = Seq(input),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: AsAsyncResetPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given AsClockPrimApi with
  def op(
    input:       Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): AsClockPrim =
    AsClockPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.asClock",
        location = location,
        operands = Seq(input),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: AsClockPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given AsSIntPrimApi with
  def op(
    input:       Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): AsSIntPrim =
    AsSIntPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.asSInt",
        location = location,
        operands = Seq(input),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: AsSIntPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = operation.getResult(0)
end given

given AsUIntPrimApi with
  def op(
    input:       Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): AsUIntPrim =
    AsUIntPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.asUInt",
        location = location,
        operands = Seq(input),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: AsUIntPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = operation.getResult(0)
end given

given BitsPrimApi with
  def op(
    input:       Value,
    hi:          BigInt,
    lo:          BigInt,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): BitsPrim =
    BitsPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.bits",
        location = location,
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::IntegerAttr
            namedAttributeApi.namedAttributeGet(
              "hi".identifierGet,
              hi.toLong.integerAttrGet(32.integerTypeGet)
            ),
            // ::mlir::IntegerAttr
            namedAttributeApi
              .namedAttributeGet("lo".identifierGet, lo.toLong.integerAttrGet(32.integerTypeGet))
          )
        ,
        operands = Seq(input),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: BitsPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given CatPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): CatPrim =
    CatPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.cat",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: CatPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given ConstantApi with
  def op(
    input:       BigInt,
    width:       Int,
    signed:      Boolean,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): Constant =
    if (!signed)
      require(input >= 0)

    val valLength =
      // infer the constant width with the input value width.
      if (width == -1)
        if (signed) input.bitLength + 1 else scala.math.max(input.bitLength, 1)
      else width
    val valType    = if (signed) valLength.integerTypeSignedGet else valLength.integerTypeUnsignedGet
    val resultType =
      if (signed) valLength.getSInt else valLength.getUInt
    Constant(
      summon[OperationApi].operationCreate(
        name = "firrtl.constant",
        location = location,
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::IntegerAttr
            namedAttributeApi
              .namedAttributeGet(
                "value".identifierGet,
                input.attrGetIntegerFromString(
                  valType,
                  Some(valLength)
                )
              )
          )
        ,
        resultsTypes = Some(
          Seq(
            resultType
          )
        )
      )
    )
  extension (ref: Constant)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)
end given

given CvtPrimApi with
  def op(
    input:       Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): CvtPrim =
    CvtPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.cvt",
        location = location,
        operands = Seq(input),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: CvtPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given DShlPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): DShlPrim =
    DShlPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.dshl",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: DShlPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given DShrPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): DShrPrim =
    DShrPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.dshr",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: DShrPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)
end given

given DivPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): DivPrim =
    DivPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.div",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: DivPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given EQPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): EQPrim =
    EQPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.eq",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: EQPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given GEQPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): GEQPrim =
    GEQPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.geq",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: GEQPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given GTPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): GTPrim =
    GTPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.gt",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: GTPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given HeadPrimApi with
  def op(
    input:       Value,
    amount:      BigInt,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): HeadPrim =
    HeadPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.head",
        location = location,
        operands = Seq(input),
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::IntegerAttr
            namedAttributeApi
              .namedAttributeGet("amount".identifierGet, amount.attrGetIntegerFromString(32.integerTypeGet))
          )
        ,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: HeadPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)
end given

given InvalidValueApi with
  def op(
    tpe:         Type,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): InvalidValue = InvalidValue(
    summon[OperationApi].operationCreate(
      name = "firrtl.invalidvalue",
      location = location,
      resultsTypes = Some(Seq(tpe))
    )
  )
  extension (ref: InvalidValue)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given LEQPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): LEQPrim =
    LEQPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.leq",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: LEQPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given LTPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): LTPrim =
    LTPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.lt",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: LTPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given MulPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): MulPrim =
    MulPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.mul",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: MulPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given MuxPrimApi with
  def op(
    sel:         Value,
    high:        Value,
    low:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): MuxPrim =
    MuxPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.mux",
        location = location,
        operands = Seq(sel, high, low),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: MuxPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given NEQPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): NEQPrim =
    NEQPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.neq",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: NEQPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given NegPrimApi with
  def op(
    input:       Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): NegPrim =
    NegPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.neg",
        location = location,
        operands = Seq(input),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: NegPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given NotPrimApi with
  def op(
    input:       Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): NotPrim =
    NotPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.not",
        location = location,
        operands = Seq(input),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: NotPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)
end given

given OpenSubfieldApi with
  def op(
    input:       Value,
    fieldIndex:  BigInt,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): Subfield =
    Subfield(
      summon[OperationApi].operationCreate(
        name = "firrtl.opensubfield",
        location = location,
        operands = Seq(input),
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::IntegerAttr
            namedAttributeApi
              .namedAttributeGet(
                "fieldIndex".identifierGet,
                fieldIndex.attrGetIntegerFromString(32.integerTypeGet)
              )
          )
        ,
        inferredResultsTypes = Some(1)
      )
    )

  extension (ref: OpenSubfield)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)
end given

given OrPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): OrPrim =
    OrPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.or",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: OrPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given OrRPrimApi with
  def op(
    input:       Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): OrRPrim =
    OrRPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.orr",
        location = location,
        operands = Seq(input),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: OrRPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)
end given

given PadPrimApi with
  def op(
    input:       Value,
    amount:      BigInt,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): PadPrim =
    PadPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.pad",
        location = location,
        operands = Seq(input),
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::IntegerAttr
            namedAttributeApi
              .namedAttributeGet("amount".identifierGet, amount.attrGetIntegerFromString(32.integerTypeGet))
          )
        ,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: PadPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)
end given

given RefCastApi with
  def op(
    input:       Value,
    tpe:         Type,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): RefCast =
    RefCast(
      summon[OperationApi].operationCreate(
        name = "firrtl.ref.cast",
        location = location,
        operands = Seq(input),
        resultsTypes = Some(Seq(tpe))
      )
    )
  extension (ref: RefCast)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)
end given

given RefResolveApi with
  def op(
    ref:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): RefResolve =
    RefResolve(
      summon[OperationApi].operationCreate(
        name = "firrtl.ref.resolve",
        location = location,
        operands = Seq(ref),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: RefResolve)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)
end given

given RefSendApi with
  def op(
    ref:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): RefSend =
    RefSend(
      summon[OperationApi].operationCreate(
        name = "firrtl.ref.send",
        location = location,
        operands = Seq(ref),
        inferredResultsTypes = Some(1)
      )
    )
  def op(
    ref:         Value,
    layer:       Seq[String],
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): RefSend =
    RefSend(
      summon[OperationApi].operationCreate(
        name = "firrtl.ref.send",
        location = location,
        operands = Seq(ref),
        resultsTypes = Some(Seq(ref.getType.getRef(false, layer)))
      )
    )
  extension (ref: RefSend)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)
end given

given RefSubApi with
  def op(
    input:       Value,
    index:       BigInt,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): RefSub =
    RefSub(
      summon[OperationApi].operationCreate(
        name = "firrtl.ref.sub",
        location = location,
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::IntegerAttr
            namedAttributeApi
              .namedAttributeGet("index".identifierGet, index.attrGetIntegerFromString(32.integerTypeGet))
          )
        ,
        operands = Seq(input),
        inferredResultsTypes = Some(1)
      )
    )

  extension (ref: RefSub)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)
end given

given RemPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): RemPrim =
    RemPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.rem",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: RemPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given ShlPrimApi with
  def op(
    input:       Value,
    amount:      BigInt,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): ShlPrim =
    ShlPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.shl",
        location = location,
        operands = Seq(input),
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::IntegerAttr
            namedAttributeApi
              .namedAttributeGet("amount".identifierGet, amount.attrGetIntegerFromString(32.integerTypeGet))
          )
        ,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: ShlPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given ShrPrimApi with
  def op(
    input:       Value,
    amount:      BigInt,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): ShrPrim =
    ShrPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.shr",
        location = location,
        operands = Seq(input),
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::IntegerAttr
            namedAttributeApi
              .namedAttributeGet("amount".identifierGet, amount.attrGetIntegerFromString(32.integerTypeGet))
          )
        ,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: ShrPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given SubPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): SubPrim =
    SubPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.sub",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: SubPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given SubaccessApi with
  def op(
    input:       Value,
    index:       Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): Subaccess =
    Subaccess(
      summon[OperationApi].operationCreate(
        name = "firrtl.subaccess",
        location = location,
        operands = Seq(input, index),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: Subaccess)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given SubfieldApi with
  def op(
    input:       Value,
    fieldIndex:  BigInt,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): Subfield =
    Subfield(
      summon[OperationApi].operationCreate(
        name = "firrtl.subfield",
        location = location,
        operands = Seq(input),
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::IntegerAttr
            namedAttributeApi
              .namedAttributeGet(
                "fieldIndex".identifierGet,
                fieldIndex.attrGetIntegerFromString(32.integerTypeGet)
              )
          )
        ,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: Subfield)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)
end given

given SubindexApi with
  def op(
    input:       Value,
    index:       BigInt,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): Subindex =
    Subindex(
      summon[OperationApi].operationCreate(
        name = "firrtl.subindex",
        location = location,
        operands = Seq(input),
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::IntegerAttr
            namedAttributeApi
              .namedAttributeGet("index".identifierGet, index.attrGetIntegerFromString(32.integerTypeGet))
          )
        ,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: Subindex)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given TailPrimApi with
  def op(
    input:       Value,
    amount:      BigInt,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): TailPrim =
    TailPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.tail",
        location = location,
        operands = Seq(input),
        namedAttributes =
          val namedAttributeApi = summon[NamedAttributeApi]
          Seq(
            // ::mlir::IntegerAttr
            namedAttributeApi
              .namedAttributeGet("amount".identifierGet, amount.attrGetIntegerFromString(32.integerTypeGet))
          )
        ,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: TailPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given XorPrimApi with
  def op(
    lhs:         Value,
    rhs:         Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): XorPrim =
    XorPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.xor",
        location = location,
        operands = Seq(lhs, rhs),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: XorPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given

given XorRPrimApi with
  def op(
    input:       Value,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): XorRPrim =
    XorRPrim(
      summon[OperationApi].operationCreate(
        name = "firrtl.xorr",
        location = location,
        operands = Seq(input),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: XorRPrim)
    def operation: Operation = ref._operation
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)

end given
