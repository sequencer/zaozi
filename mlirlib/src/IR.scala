// SPDX-License-Identifier: Apache-2.0
package org.llvm.mlir.scalalib

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.*

import java.lang.foreign.{Arena, MemorySegment}

given ContextApi with
  inline def contextCreate(
    using arena: Arena
  ): Context =
    Context(mlirContextCreate(arena))

  inline def contextCreateWithThreading(
    threadingEnabled: Boolean
  )(
    using arena:      Arena
  ): Context =
    Context(mlirContextCreateWithThreading(arena, threadingEnabled))

  inline def contextCreateWithRegistry(
    registry:         DialectRegistry,
    threadingEnabled: Boolean
  )(
    using arena:      Arena
  ): Context =
    Context(mlirContextCreateWithRegistry(arena, registry.segment, threadingEnabled))

  extension (context: Context)
    inline def getOrLoadDialect(
      name:        String
    )(
      using arena: Arena
    ): Dialect = Dialect(mlirContextGetOrLoadDialect(arena, context.segment, name.toStringRef.segment))
    inline def destroy():                                        Unit = mlirContextDestroy(context.segment)
    inline def allowUnregisteredDialects(allow: Boolean):        Unit =
      mlirContextSetAllowUnregisteredDialects(context.segment, allow)
    inline def appendDialectRegistry(registry: DialectRegistry): Unit =
      mlirContextAppendDialectRegistry(context.segment, registry.segment)
    inline def enableMultithreading(enable: Boolean):            Unit =
      mlirContextEnableMultithreading(context.segment, enable)
    inline def loadAllAvailableDialects():                       Unit =
      mlirContextLoadAllAvailableDialects(context.segment)
    inline def setThreadPool(threadPool: LlvmThreadPool):        Unit =
      mlirContextSetThreadPool(context.segment, threadPool.segment)

    inline def segment: MemorySegment = context._segment
    inline def sizeOf:  Int           = MlirContext.sizeof().toInt

end given

given DialectApi with
  extension (dialect: Dialect)
    inline def segment: MemorySegment = dialect._segment
    inline def sizeOf:  Int           = MlirDialect.sizeof().toInt
end given

given DialectHandleApi with
  extension (dialectHandle: DialectHandle)
    inline def getNamespace(
    )(
      using arena: Arena
    ): String = StringRef(mlirDialectHandleGetNamespace(arena, dialectHandle.segment)).toScalaString
    inline def loadDialect(
      using arena: Arena,
      context:     Context
    ): Unit = mlirDialectHandleLoadDialect(arena, dialectHandle.segment, context.segment)
    inline def insertDialect(dialectRegistry: DialectRegistry): Unit          =
      mlirDialectHandleInsertDialect(dialectHandle.segment, dialectRegistry.segment)
    inline def insertDialect(
    )(
      using context: Context
    ): Unit =
      mlirDialectHandleRegisterDialect(dialectHandle.segment, context.segment)
    inline def segment:                                         MemorySegment = dialectHandle._segment
    inline def sizeOf:                                          Int           = MlirDialectHandle.sizeof().toInt
end given

given DialectRegistryApi with
  inline def registryCreate(
  )(
    using arena: Arena
  ): DialectRegistry = DialectRegistry(mlirDialectRegistryCreate(arena))

  extension (dialectRegistry: DialectRegistry)
    inline def destroy(): Unit          = mlirDialectRegistryDestroy(dialectRegistry.segment)
    inline def segment:   MemorySegment = dialectRegistry._segment
    inline def sizeOf:    Int           = MlirDialectRegistry.sizeof().toInt
end given

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
    inline def locationGetContext(
      using arena: Arena
    ): Context = Context(mlirLocationGetContext(arena, location.segment))
    inline def segment: MemorySegment = location._segment
    inline def sizeOf:  Int           = MlirLocation.sizeof().toInt
end given

given ModuleApi with
  inline def moduleCreateEmpty(
    location:    Location
  )(
    using arena: Arena
  ): Module = new Module(mlirModuleCreateEmpty(arena, location.segment))

  inline def moduleCreateParse(
    module:      String
  )(
    using arena: Arena,
    context:     Context
  ): Module = new Module(mlirModuleCreateParse(arena, context.segment, module.toStringRef.segment))

  inline def moduleFromOperation(
    op:          Operation
  )(
    using arena: Arena
  ): Module = new Module(mlirModuleFromOperation(arena, op.segment))

  extension (module: Module)
    inline def getContext(
    )(
      using arena: Arena
    ): Context = Context(mlirModuleGetContext(arena, module.segment))
    inline def getBody(
      using arena: Arena
    ) = Block(mlirModuleGetBody(arena, segment))
    inline def getOperation(
      using arena: Arena
    ): Operation = Operation(mlirModuleGetOperation(arena, module.segment))
    inline def destroy(): Unit          = mlirModuleDestroy(module.segment)
    inline def segment:   MemorySegment = module._segment
    inline def sizeOf:    Int           = MlirModule.sizeof().toInt
end given

given OperationStateApi with
  inline def operationStateGet(
    name:        String,
    loc:         Location
  )(
    using arena: Arena
  ): OperationState =
    OperationState(mlirOperationStateGet(arena, name.toStringRef.segment, loc.segment))

  extension (operationState: OperationState)
    inline def addResults(
      results:     Seq[Type]
    )(
      using arena: Arena
    ): Unit =
      mlirOperationStateAddResults(operationState.segment, results.size, results.toMlirArray)
    inline def addOperands(
      operands:    Seq[Value]
    )(
      using arena: Arena
    ): Unit =
      mlirOperationStateAddOperands(operationState.segment, operands.size, operands.toMlirArray)
    inline def addOwnedRegions(
      regions:     Seq[Region]
    )(
      using arena: Arena
    ): Unit =
      mlirOperationStateAddOwnedRegions(operationState.segment, regions.size, regions.toMlirArray)
    inline def addSuccessors(
      blocks:      Seq[Block]
    )(
      using arena: Arena
    ): Unit =
      mlirOperationStateAddSuccessors(operationState.segment, blocks.size, blocks.toMlirArray)
    inline def addAttributes(
      attrs:       Seq[NamedAttribute]
    )(
      using arena: Arena
    ): Unit =
      mlirOperationStateAddAttributes(operationState.segment, attrs.size, attrs.toMlirArray)
    inline def enableResultTypeInference(): Unit          =
      mlirOperationStateEnableResultTypeInference(operationState.segment)
    inline def segment:                     MemorySegment = operationState._segment
    inline def sizeOf:                      Int           = MlirOperationState.sizeof().toInt
end given

given AsmStateApi with
  inline def asmStateCreateForOperation(
    op:          Operation,
    flags:       OpPrintingFlags
  )(
    using arena: Arena
  ): MemorySegment = mlirAsmStateCreateForOperation(arena, op.segment, flags.segment)
  inline def asmStateCreateForValue(
    value:       Value,
    flags:       OpPrintingFlags
  )(
    using arena: Arena
  ): MemorySegment = mlirAsmStateCreateForValue(arena, value.segment, flags.segment)
  extension (asmState: AsmState)
    inline def destroy(): Unit          = mlirAsmStateDestroy(asmState.segment)
    inline def segment:   MemorySegment = asmState._segment
    inline def sizeOf:    Int           = MlirAsmState.sizeof().toInt
end given

given OpPrintingFlagsApi with
  inline def opPrintingFlagsCreate(
  )(
    using arena: Arena
  ): OpPrintingFlags = OpPrintingFlags(mlirOpPrintingFlagsCreate(arena))

  extension (opPrintingFlags: OpPrintingFlags)
    inline def flagsDestroy():                                             Unit          = mlirOpPrintingFlagsDestroy(opPrintingFlags.segment)
    inline def flagsElideLargeElementsAttrs(largeElementLimit: Long):      Unit          =
      mlirOpPrintingFlagsElideLargeElementsAttrs(opPrintingFlags.segment, largeElementLimit)
    inline def flagsElideLargeResourceString(largeResourceLimit: Long):    Unit          =
      mlirOpPrintingFlagsElideLargeResourceString(opPrintingFlags.segment, largeResourceLimit)
    inline def flagsEnableDebugInfo(enable: Boolean, prettyForm: Boolean): Unit          =
      mlirOpPrintingFlagsEnableDebugInfo(opPrintingFlags.segment, enable, prettyForm)
    inline def flagsPrintGenericOpForm():                                  Unit          = mlirOpPrintingFlagsPrintGenericOpForm(opPrintingFlags.segment)
    inline def flagsUseLocalScope():                                       Unit          = mlirOpPrintingFlagsUseLocalScope(opPrintingFlags.segment)
    inline def flagsAssumeVerified():                                      Unit          = mlirOpPrintingFlagsAssumeVerified(opPrintingFlags.segment)
    inline def flagsSkipRegions():                                         Unit          = mlirOpPrintingFlagsSkipRegions(opPrintingFlags.segment)
    inline def segment:                                                    MemorySegment = opPrintingFlags._segment
    inline def sizeOf:                                                     Int           = MlirOpPrintingFlags.sizeof().toInt
end given

given BytecodeWriterConfigApi with
  inline def bytecodeWriterConfigCreate(
  )(
    using arena: Arena
  ) = BytecodeWriterConfig(mlirBytecodeWriterConfigCreate(arena))
  extension (bytecodeWriterConfig: BytecodeWriterConfig)
    inline def destroy():                         Unit          = mlirBytecodeWriterConfigDestroy(bytecodeWriterConfig.segment)
    inline def desiredEmitVersion(version: Long): Unit          =
      mlirBytecodeWriterConfigDesiredEmitVersion(bytecodeWriterConfig.segment, version)
    inline def segment:                           MemorySegment = bytecodeWriterConfig._segment
    inline def sizeOf:                            Int           = MlirBytecodeWriterConfig.sizeof().toInt
end given

given OperationApi with
  inline def operationCreate(
    state:       OperationState
  )(
    using arena: Arena
  ): Operation = Operation(mlirOperationCreate(arena, state.segment))
  inline def operationCreateParse(
    sourceStr:   String,
    sourceName:  String
  )(
    using arena: Arena,
    context:     Context
  ): Operation = Operation(
    mlirOperationCreateParse(arena, context.segment, sourceStr.toStringRef.segment, sourceName.toStringRef.segment)
  )
  inline def operationClone(
    op:          Operation
  )(
    using arena: Arena
  ): Operation = Operation(mlirOperationClone(arena, op.segment))
  extension (operation: Operation)
    inline def getContext(
    )(
      using arena: Arena
    ): Context = Context(mlirOperationGetContext(arena, operation.segment))
    inline def getLocation(
    )(
      using arena: Arena
    ): Location = Location(mlirOperationGetLocation(arena, operation.segment))
    inline def getTypeID(
    )(
      using arena: Arena
    ): TypeID = TypeID(mlirOperationGetTypeID(arena, operation.segment))
    inline def getName(
    )(
      using arena: Arena
    ): Identifier = Identifier(mlirOperationGetName(arena, operation.segment))
    inline def getBlock(
    )(
      using arena: Arena
    ): Block = Block(mlirOperationGetBlock(arena, operation.segment))
    inline def getParentOperation(
    )(
      using arena: Arena
    ): Operation = Operation(mlirOperationGetParentOperation(arena, operation.segment))
    inline def getRegion(
      pos:         Long
    )(
      using arena: Arena
    ): Region = Region(mlirOperationGetRegion(arena, operation.segment, pos))
    inline def getNextInBlock(
    )(
      using arena: Arena
    ): Operation = Operation(mlirOperationGetNextInBlock(arena, operation.segment))
    inline def getOperand(
      pos:         Long
    )(
      using arena: Arena
    ): Value = Value(mlirOperationGetOperand(arena, operation.segment, pos))
    inline def getResult(
      pos:         Long
    )(
      using arena: Arena
    ): Value = Value(mlirOperationGetResult(arena, operation.segment, pos))
    inline def getSuccessor(
      pos:         Long
    )(
      using arena: Arena
    ): Block = Block(mlirOperationGetSuccessor(arena, operation.segment, pos))
    inline def getInherentAttributeByName(
      name:        String
    )(
      using arena: Arena
    ): Attribute = Attribute(
      mlirOperationGetInherentAttributeByName(arena, operation.segment, name.toStringRef.segment)
    )
    inline def getDiscardableAttribute(
      pos:         Long
    )(
      using arena: Arena
    ): NamedAttribute = NamedAttribute(mlirOperationGetDiscardableAttribute(arena, operation.segment, pos))
    inline def getDiscardableAttributeByName(
      name:        String
    )(
      using arena: Arena
    ): Attribute = Attribute(
      mlirOperationGetDiscardableAttributeByName(arena, operation.segment, name.toStringRef.segment)
    )
    inline def getAttribute(
      pos:         Long
    )(
      using arena: Arena
    ): NamedAttribute = NamedAttribute(mlirOperationGetAttribute(arena, operation.segment, pos))
    inline def getAttributeByName(
      name:        String
    )(
      using arena: Arena
    ): Attribute = Attribute(mlirOperationGetAttributeByName(arena, name.toStringRef.segment, operation.segment))
    inline def writeBytecodeWithConfig(
      config:      BytecodeWriterConfig,
      callback:    Array[Byte] => Unit
    )(
      using arena: Arena
    ): LogicalResult = LogicalResult(
      mlirOperationWriteBytecodeWithConfig(
        arena,
        operation.segment,
        config.segment,
        callback.bytesToStringCallback.segment,
        MemorySegment.NULL
      )
    )
    inline def getFirstRegion(
    )(
      using arena: Arena
    ): LogicalResult = LogicalResult(mlirOperationGetFirstRegion(arena, operation.segment))

    inline def destroy():                              Unit = mlirOperationDestroy(operation.segment)
    inline def removeFromParent():                     Unit = mlirOperationRemoveFromParent(operation.segment)
    inline def setOperand(pos: Long, newValue: Value): Unit =
      mlirOperationSetOperand(operation.segment, pos, newValue.segment)
    inline def setOperands(
      operands: Seq[Value]
    )(
      using Arena
    ): Unit = mlirOperationSetOperands(operation.segment, operands.size, operands.toMlirArray)
    inline def setSuccessor(pos: Long, block: Block):  Unit =
      mlirOperationSetSuccessor(operation.segment, pos, block.segment)
    inline def setInherentAttributeByName(
      name: String,
      attr: Attribute
    )(
      using Arena
    ): Unit = mlirOperationSetInherentAttributeByName(operation.segment, name.toStringRef.segment, attr.segment)
    inline def setDiscardableAttributeByName(
      name: String,
      attr: Attribute
    )(
      using Arena
    ): Unit = mlirOperationSetDiscardableAttributeByName(operation.segment, name.toStringRef.segment, attr.segment)
    inline def setAttributeByName(
      name: String,
      attr: Attribute
    )(
      using Arena
    ): Unit = mlirOperationSetAttributeByName(operation.segment, name.toStringRef.segment, attr.segment)
    inline def print(
      callback: String => Unit
    )(
      using Arena
    ): Unit = mlirOperationPrint(operation.segment, callback.stringToStringCallback.segment, MemorySegment.NULL)
    inline def printWithFlags(
      callback: String => Unit
    )(
      using Arena
    ): Unit = mlirOperationPrint(operation.segment, callback.stringToStringCallback.segment, MemorySegment.NULL)
    inline def printWithState(
      asmState: AsmState,
      callback: String => Unit
    )(
      using Arena
    ): Unit = mlirOperationPrintWithState(
      operation.segment,
      asmState.segment,
      callback.stringToStringCallback.segment,
      MemorySegment.NULL
    )
    inline def writeBytecode(
      callBack:    Array[Byte] => Unit
    )(
      using arena: Arena
    ): Unit = mlirOperationWriteBytecode(operation.segment, callBack.bytesToStringCallback.segment, MemorySegment.NULL)

    inline def dump(): Unit = mlirOperationDump(operation.segment)
    inline def moveAfter(other:  Operation): Unit = mlirOperationMoveAfter(operation.segment, other.segment)
    inline def moveBefore(other: Operation): Unit = mlirOperationMoveBefore(operation.segment, other.segment)
    inline def walk(
      callback:    Operation => WalkResultEnum,
      walk:        WalkEnum
    )(
      using arena: Arena
    ): Unit =
      mlirOperationWalk(operation.segment, callback.toOperationWalkCallback.segment, MemorySegment.NULL, walk.toNative)
    inline def segment: MemorySegment = operation._segment
    inline def sizeOf: Int = MlirOperation.sizeof().toInt
end given
given WalkResultEnumApi with
  extension (int: Int)
    inline def fromNative: WalkResultEnum = int match
      case i if i == MlirWalkResultAdvance()   => WalkResultEnum.Advance
      case i if i == MlirWalkResultInterrupt() => WalkResultEnum.Interrupt
      case i if i == MlirWalkResultSkip()      => WalkResultEnum.Skip
  extension (ref: WalkResultEnum)
    inline def toNative: Int = ref match
      case WalkResultEnum.Advance   => MlirWalkResultAdvance()
      case WalkResultEnum.Interrupt => MlirWalkResultInterrupt()
      case WalkResultEnum.Skip      => MlirWalkResultSkip()
    inline def sizeOf:   Int = 4
end given

given WalkEnumApi with
  extension (int: Int)
    inline def fromNative: WalkEnum = int match
      case i if i == MlirWalkPostOrder() => WalkEnum.PostOrder
      case i if i == MlirWalkPreOrder()  => WalkEnum.PreOrder
  extension (ref: WalkEnum)
    inline def toNative: Int = ref match
      case WalkEnum.PostOrder => MlirWalkPostOrder()
      case WalkEnum.PreOrder  => MlirWalkPreOrder()
    inline def sizeOf:   Int = 4
end given

given RegionApi with
  inline def regionCreate(
    using arena: Arena
  ): Region =
    Region(mlirRegionCreate(arena))

  extension (region: Region)
    inline def getFirstBlock(
    )(
      using arena: Arena
    ): Block = Block(mlirRegionGetFirstBlock(arena, region.segment))
    inline def getNextInOperation(
    )(
      using arena: Arena
    ): Region = Region(mlirRegionGetNextInOperation(arena, region.segment))
    inline def destroy(
    )(
      using arena: Arena
    ): Unit = mlirRegionDestroy(region.segment)
    inline def appendOwnedBlock(block: Block):                         Unit          =
      mlirRegionAppendOwnedBlock(region.segment, block.segment)
    inline def insertOwnedBlock(pos: Long, block: Block):              Unit          =
      mlirRegionInsertOwnedBlock(region.segment, pos, block.segment)
    inline def insertOwnedBlockAfter(reference: Block, block: Block):  Unit          =
      mlirRegionInsertOwnedBlockAfter(region.segment, reference.segment, block.segment)
    inline def insertOwnedBlockBefore(reference: Block, block: Block): Unit          =
      mlirRegionInsertOwnedBlockBefore(region.segment, reference.segment, block.segment)
    inline def segment:                                                MemorySegment = region._segment
    inline def sizeOf:                                                 Int           = MlirRegion.sizeof().toInt

end given

given BlockApi with
  inline def blockCreate(
    args:        Seq[Type],
    locs:        Seq[Location]
  )(
    using arena: Arena
  ): Block =
    Block(mlirBlockCreate(arena, args.length, args.toMlirArray, locs.toMlirArray))

  extension (block: Block)
    inline def getParentOperation(
    )(
      using arena: Arena
    ): Operation = Operation(mlirBlockGetParentOperation(arena, block.segment))
    inline def getNextInRegion(
    )(
      using arena: Arena
    ): Block = Block(mlirBlockGetNextInRegion(arena, block.segment))
    inline def getFirstOperation(
    )(
      using arena: Arena
    ): Operation = Operation(mlirBlockGetFirstOperation(arena, block.segment))
    inline def getTerminator(
    )(
      using arena: Arena
    ): Operation = Operation(mlirBlockGetTerminator(arena, block.segment))
    inline def addArgument(
      tpe:         Type,
      loc:         Location
    )(
      using arena: Arena
    ): Operation = Operation(mlirBlockAddArgument(arena, block.segment, tpe.segment, loc.segment))
    inline def insertArgument(
      pos:         Int,
      tpe:         Type,
      loc:         Location
    )(
      using arena: Arena
    ): Operation = Operation(mlirBlockInsertArgument(arena, block.segment, pos, tpe.segment, loc.segment))
    inline def getArgument(
      pos:         Long
    )(
      using arena: Arena
    ): Value = Value(mlirBlockGetArgument(arena, block.segment, pos))
    inline def argumentGetOwner(
    )(
      using arena: Arena
    ): Block = Block(mlirBlockArgumentGetOwner(arena, block.segment))
    inline def destroy():                                                              Unit = mlirBlockDestroy(block.segment)
    inline def detach():                                                               Unit = mlirBlockDetach(block.segment)
    inline def appendOwnedOperation(operation: Operation):                             Unit =
      mlirBlockAppendOwnedOperation(block.segment, operation.segment)
    inline def insertOwnedOperation(pos: Long, operation: Operation):                  Unit =
      mlirBlockInsertOwnedOperation(block.segment, pos, operation.segment)
    inline def insertOwnedOperationAfter(reference: Operation, operation: Operation):  Unit =
      mlirBlockInsertOwnedOperationAfter(block.segment, reference.segment, operation.segment)
    inline def insertOwnedOperationBefore(reference: Operation, operation: Operation): Unit =
      mlirBlockInsertOwnedOperationBefore(block.segment, reference.segment, operation.segment)
    inline def eraseArgument(index: Int): Unit = mlirBlockEraseArgument(block.segment, index)
    inline def print(
      callBack:    String => Unit
    )(
      using arena: Arena
    ): Unit = mlirBlockPrint(block.segment, callBack.stringToStringCallback.segment, MemorySegment.NULL)
    inline def segment: MemorySegment = block._segment
    inline def sizeOf: Int = MlirBlock.sizeof().toInt

end given

given ValueApi with
  extension (value: Value)
    inline def getType(
      using arena: Arena
    ): Type = Type(mlirValueGetType(arena, value.segment))
    inline def getFirstUse(
      using arena: Arena
    ): Type = Type(mlirValueGetFirstUse(arena, value.segment))
    inline def setType(tpe: Type): Unit = mlirValueSetType(value.segment, tpe.segment)
    inline def dump():  Unit          = mlirValueDump(value.segment)
    inline def print(
      callback:    String => Unit
    )(
      using arena: Arena
    ): Unit = mlirValuePrint(value.segment, callback.stringToStringCallback.segment, MemorySegment.NULL)
    inline def printAsOperand(
      state:       AsmState,
      callback:    String => Unit
    )(
      using arena: Arena
    ): Unit =
      mlirValuePrintAsOperand(value.segment, state.segment, callback.stringToStringCallback.segment, MemorySegment.NULL)
    inline def replaceAllUsesOfWith(w: Value): Unit = mlirValueReplaceAllUsesOfWith(value.segment, w.segment)
    inline def segment: MemorySegment = value._segment
    inline def sizeOf:  Int           = MlirValue.sizeof().toInt
end given

given OpOperandApi with
  extension (opOperandApi: OpOperand)
    inline def segment: MemorySegment = opOperandApi._segment
    inline def sizeOf:  Int           = MlirOpOperand.sizeof().toInt
end given

given TypeApi with
  inline def f64Type(
    using arena: Arena,
    context:     Context
  ): Type = Type(mlirF64TypeGet(arena, context.segment))

  inline def noneType(
    using arena: Arena,
    context:     Context
  ) = Type(mlirNoneTypeGet(arena, context.segment))

  extension (width: Int)
    inline def toSignedInteger(
      using arena: Arena,
      context:     Context
    ): Type = Type(mlirIntegerTypeSignedGet(arena, context.segment, width))
    inline def toUnsignedInteger(
      using arena: Arena,
      context:     Context
    ): Type = Type(mlirIntegerTypeUnsignedGet(arena, context.segment, width))
    inline def toIntegerType(
      using arena: Arena,
      context:     Context
    ): Type = Type(mlirIntegerTypeGet(arena, context.segment, width))
  extension (tpe:   Type)
    inline def segment: MemorySegment = tpe._segment
    inline def sizeOf:  Int           = MlirType.sizeof().toInt
end given

given AttributeApi with
  inline def createUnitAttribute(
    using arena: Arena,
    context:     Context
  ): Attribute = Attribute(mlirUnitAttrGet(arena, context.segment))

  inline def allocateAttribute(
    using arena: Arena
  ): Attribute = Attribute(MlirAttribute.allocate(arena))

  extension (array:  Seq[Attribute])
    inline def toAttributeArrayAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute =
      Attribute(mlirArrayAttrGet(arena, context.segment, array.size, array.toMlirArray))
  extension (tpe:    Type)
    inline def toTypeAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute =
      Attribute(mlirTypeAttrGet(arena, tpe.segment))
  extension (bool:   Boolean)
    inline def toBooleanAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute =
      Attribute(mlirBoolAttrGet(arena, context.segment, if (bool) 1 else 0))
  extension (string: String)
    inline def toStringAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(mlirStringAttrGet(arena, context.segment, string.toStringRef.segment))
    inline def toSymbolRefAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(mlirFlatSymbolRefAttrGet(arena, context.segment, string.toStringRef.segment))

  extension (double: Double)
    inline def toDoubleAttribute(
      tpe:         Type
    )(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(mlirFloatAttrDoubleGet(arena, context.segment, tpe.segment, double))
  extension (int:    Long)
    inline def toIntegerAttribute(
      tpe:         Type
    )(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(mlirIntegerAttrGet(arena, tpe.segment, int))

  extension (attribute: Attribute)
    inline def dump():      Unit          = mlirAttributeDump(attribute.segment)
    inline def numElements: Int           = mlirArrayAttrGetNumElements(attribute.segment).toInt
    inline def element(
      idx:         Int
    )(
      using arena: Arena
    ): Attribute = Attribute(mlirArrayAttrGetElement(arena, attribute.segment, idx.toLong))
    inline def getString(
      using arena: Arena
    ): String =
      StringRef(mlirStringAttrGetValue(arena, attribute.segment)).toScalaString
    inline def getInt:      Long          =
      mlirIntegerAttrGetValueInt(attribute.segment)
    inline def getSInt:     Long          =
      mlirIntegerAttrGetValueSInt(attribute.segment)
    inline def getUInt:     Long          =
      mlirIntegerAttrGetValueUInt(attribute.segment)
    inline def isInteger:   Boolean       =
      mlirAttributeIsAInteger(attribute.segment)
    inline def isString:    Boolean       =
      mlirAttributeIsAString(attribute.segment)
    inline def segment:     MemorySegment = attribute._segment
    inline def sizeOf:      Int           = MlirAttribute.sizeof().toInt

end given

given NamedAttributeApi with
  inline def namedAttributeGet(
    identifier:  Identifier,
    attribute:   Attribute
  )(
    using arena: Arena
  ): NamedAttribute = NamedAttribute(mlirNamedAttributeGet(arena, identifier.segment, attribute.segment))

  extension (namedAttribute: NamedAttribute)
    inline def segment: MemorySegment = namedAttribute._segment
    inline def sizeOf:  Int           = MlirNamedAttribute.sizeof().toInt
end given

given IdentifierApi with
  extension (identifierString: String)
    inline def identifierGet(
      using arena: Arena,
      context:     Context
    ): Identifier =
      Identifier(mlirIdentifierGet(arena, context._segment, identifierString.toStringRef.segment))
  extension (identifier:       Identifier)
    inline def getContext(
    )(
      using arena: Arena
    ): Context = Context(mlirIdentifierGetContext(arena, identifier.segment))
    inline def str(
    )(
      using arena: Arena
    ): String = StringRef(mlirIdentifierStr(arena, identifier.segment)).toScalaString
    inline def segment: MemorySegment = identifier._segment
    inline def sizeOf:  Int           = MlirIdentifier.sizeof().toInt
end given

given SymbolTableApi with
  extension (symbolTableApi: SymbolTable)
    inline def segment: MemorySegment = symbolTableApi._segment
    inline def sizeOf:  Int           = MlirSymbolTable.sizeof().toInt
end given
