// SPDX-License-Identifier: Apache-2.0
package org.llvm.circt.scalalib.firrtl.operation

import org.llvm.circt.scalalib.firrtl.capi.{FirrtlBundleField, FirrtlDirection, FirrtlNameKind, given}
import org.llvm.mlir.scalalib.{Block, Context, HasOperation, Location, LocationApi, NamedAttributeApi, Operation, OperationApi, Type, Value, Module as MlirModule, given}

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
    ): Block = c.operation.getFirstRegion().getFirstBlock()
    inline def appendToModule(
    )(
      using arena: Arena,
      module:      MlirModule
    ): Unit =
      module.getBody.appendOwnedOperation(c.operation)
  extension (ref: Circuit) def operation: Operation = ref._operation
end given
given ModuleApi with
  inline def op(
    name:        String,
    location:    Location,
    interface:   Seq[(FirrtlBundleField, Location)]
  )(
    using arena: Arena,
    context:     Context
  ): Module = new Module(
    summon[OperationApi].operationCreate(
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
          // ::mlir::StringAttr
          namedAttributeApi.namedAttributeGet(
            "sym_name".identifierGet,
            name.stringAttrGet
          ),
          // ::circt::firrtl::ConventionAttr
          // namedAttributeApi.namedAttributeGet("convention".identifierGet, ???),
          // ::mlir::DenseBoolArrayAttr
          namedAttributeApi.namedAttributeGet(
            "portDirections".identifierGet,
            interface
              .map:
                case (bf, _) =>
                  if (bf.getIsFlip()) FirrtlDirection.In else FirrtlDirection.Out
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
            interface.map(_._1.getName().stringAttrGet).arrayAttrGet
          ),
          // ::mlir::ArrayAttr
          namedAttributeApi.namedAttributeGet(
            "portTypes".identifierGet,
            interface.map(_._1.getType().typeAttrGet).arrayAttrGet
          )
          // ::mlir::ArrayAttr
          // namedAttributeApi.namedAttributeGet("annotations".identifierGet, ???),
          // ::mlir::ArrayAttr
          // namedAttributeApi.namedAttributeGet("layers".identifierGet, ???)
        )
    )
  )
  extension (ref: Module)
    inline def block(
      using Arena
    ): Block = operation.getFirstRegion().getFirstBlock()

    inline def getIO(
      idx: Long
    )(
      using Arena
    ): Value = block.getArgument(idx)

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
                  if (bf.getIsFlip()) FirrtlDirection.In else FirrtlDirection.Out
                .attrGetPortDirs
            ),
            // ::mlir::ArrayAttr
            namedAttributeApi.namedAttributeGet(
              "portNames".identifierGet,
              interface.map(_.getName().stringAttrGet).arrayAttrGet
            )
            // ::mlir::ArrayAttr
            // namedAttributeApi.namedAttributeGet("annotations".identifierGet, Seq().arrayAttrGet),
            // ::mlir::ArrayAttr
            // namedAttributeApi.namedAttributeGet("portAnnotations".identifierGet, Seq().arrayAttrGet),
            // ::mlir::ArrayAttr
            // namedAttributeApi.namedAttributeGet("layers".identifierGet, Seq().arrayAttrGet)
            // ::mlir::UnitAttr
            // namedAttributeApi.namedAttributeGet("lowerToBind".identifierGet, ???),
            // ::circt::hw::InnerSymAttr
            // namedAttributeApi.namedAttributeGet("inner_sym".identifierGet, ???)
          )
        ,
        resultsTypes = Some(interface.map(_.getType()))
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
            namedAttributeApi.namedAttributeGet("nameKind".identifierGet, nameKind.attrGetNameKind)
            // ::mlir::ArrayAttr
            // namedAttributeApi.namedAttributeGet("annotations".identifierGet, ???),
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
          namedAttributeApi.namedAttributeGet("nameKind".identifierGet, nameKind.attrGetNameKind)
          // ::mlir::ArrayAttr
          // namedAttributeApi.namedAttributeGet("annotations".identifierGet, ???),
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
    reset:       Value
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
          namedAttributeApi.namedAttributeGet("nameKind".identifierGet, nameKind.attrGetNameKind)
          // ::mlir::ArrayAttr
          // namedAttributeApi.namedAttributeGet("annotations".identifierGet, ???),
          // ::circt::hw::InnerSymAttr
          // namedAttributeApi.namedAttributeGet("inner_sym".identifierGet, ???),
          // ::mlir::UnitAttr
          // namedAttributeApi.namedAttributeGet("forceable".identifierGet, ???)
        )
      ,
      operands = Seq(clock, reset),
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
            namedAttributeApi.namedAttributeGet("nameKind".identifierGet, nameKind.attrGetNameKind)
            // ::mlir::ArrayAttr
            // namedAttributeApi.namedAttributeGet("annotations".identifierGet, ???),
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
    def result(
      using Arena
    ): Value = ref.operation.getResult(0)
  extension (ref: Wire) def operation: Operation = ref._operation
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
  extension (ref: AddPrim) def operation: Operation = ref._operation
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
  extension (ref: AndPrim) def operation: Operation = ref._operation
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
  extension (ref: AndRPrim) def operation: Operation = ref._operation
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
  extension (ref: AsAsyncResetPrim) def operation: Operation = ref._operation
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
  extension (ref: AsClockPrim) def operation: Operation = ref._operation
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
  extension (ref: AsSIntPrim) def operation: Operation = ref._operation
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
  extension (ref: AsUIntPrim) def operation: Operation = ref._operation
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
              hi.toLong.toIntegerAttribute(32.integerTypeUnsignedGet)
            ),
            // ::mlir::IntegerAttr
            namedAttributeApi
              .namedAttributeGet("lo".identifierGet, lo.toLong.toIntegerAttribute(32.integerTypeUnsignedGet))
          )
        ,
        operands = Seq(input),
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: BitsPrim) def operation: Operation = ref._operation
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
  extension (ref: CatPrim) def operation: Operation = ref._operation
end given

given ConstantApi with
  def op(
    input:       BigInt,
    signed:      Boolean,
    location:    Location
  )(
    using arena: Arena,
    context:     Context
  ): Constant =
    if (!signed)
      require(input >= 0)
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
                  if (signed) input.bitLength.integerTypeSignedGet else input.bitLength.integerTypeUnsignedGet
                )
              )
          )
        ,
        resultsTypes = Some(
          Seq(
            if (signed) input.bitLength.getSInt else input.bitLength.getUInt
          )
        )
      )
    )
  extension (ref: Constant) def operation: Operation = ref._operation
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
  extension (ref: CvtPrim) def operation: Operation = ref._operation
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
  extension (ref: DShlPrim) def operation: Operation = ref._operation
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
  extension (ref: DShrPrim) def operation: Operation = ref._operation
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
  extension (ref: DivPrim) def operation: Operation = ref._operation
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
  extension (ref: EQPrim) def operation: Operation = ref._operation
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
  extension (ref: GEQPrim) def operation: Operation = ref._operation
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
  extension (ref: GTPrim) def operation: Operation = ref._operation
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
              .namedAttributeGet("amount".identifierGet, amount.attrGetIntegerFromString(32.integerTypeUnsignedGet))
          )
        ,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: HeadPrim) def operation: Operation = ref._operation
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
  extension (ref: LEQPrim) def operation: Operation = ref._operation
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
  extension (ref: LTPrim) def operation: Operation = ref._operation
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
  extension (ref: MulPrim) def operation: Operation = ref._operation
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
  extension (ref: MuxPrim) def operation: Operation = ref._operation
end given

given NEQPrimApi with
  def neqPrim(
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
  extension (ref: NEQPrim) def operation: Operation = ref._operation
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
  extension (ref: NegPrim) def operation: Operation = ref._operation
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
  extension (ref: NotPrim) def operation: Operation = ref._operation
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
  extension (ref: OrPrim) def operation: Operation = ref._operation
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
  extension (ref: OrRPrim) def operation: Operation = ref._operation
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
              .namedAttributeGet("amount".identifierGet, amount.attrGetIntegerFromString(32.integerTypeUnsignedGet))
          )
        ,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: PadPrim) def operation: Operation = ref._operation
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
  extension (ref: RemPrim) def operation: Operation = ref._operation
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
              .namedAttributeGet("amount".identifierGet, amount.attrGetIntegerFromString(32.integerTypeUnsignedGet))
          )
        ,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: ShlPrim) def operation: Operation = ref._operation
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
              .namedAttributeGet("amount".identifierGet, amount.attrGetIntegerFromString(32.integerTypeUnsignedGet))
          )
        ,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: ShrPrim) def operation: Operation = ref._operation
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
  extension (ref: SubPrim) def operation: Operation = ref._operation
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
  extension (ref: Subaccess) def operation: Operation = ref._operation
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
                fieldIndex.attrGetIntegerFromString(32.integerTypeUnsignedGet)
              )
          )
        ,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: Subfield) def operation: Operation = ref._operation
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
              .namedAttributeGet("index".identifierGet, index.attrGetIntegerFromString(32.integerTypeUnsignedGet))
          )
        ,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: Subindex) def operation: Operation = ref._operation
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
              .namedAttributeGet("amount".identifierGet, amount.attrGetIntegerFromString(32.integerTypeUnsignedGet))
          )
        ,
        inferredResultsTypes = Some(1)
      )
    )
  extension (ref: TailPrim) def operation: Operation = ref._operation
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
  extension (ref: XorPrim) def operation: Operation = ref._operation
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
  extension (ref: XorRPrim) def operation: Operation = ref._operation
end given