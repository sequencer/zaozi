// SPDX-License-Identifier: Apache-2.0
package org.llvm.mlir.scalalib

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.*

import java.lang.foreign.{Arena, MemorySegment}

given [E]: ToMlirArray[E] with
  extension (xs: Seq[E])
    def toMlirArray(
      using arena: Arena,
      api:         HasSizeOf[E] & HasSegment[E]
    ): (MemorySegment, Int) =
      if (xs.nonEmpty)
        val sizeOfT: Int = xs.head.sizeOf
        val buffer = arena.allocate(sizeOfT * xs.length)
        xs.zipWithIndex.foreach:
          case (x, i) =>
            buffer.asSlice(sizeOfT * i, sizeOfT).copyFrom(x.segment)
        (buffer, xs.length)
      else (MemorySegment.NULL, 0)
end given

given StringCallBackApi with
  extension (stringCallBack: String => Unit)
    def toStringCallBack(
      using arena: Arena
    ): StringCallBack =
      val cb = new MlirStringCallback:
        def apply(message: MemorySegment, userData: MemorySegment): Unit =
          stringCallBack(StringRef(message).toScalaString)
      StringCallBack(MlirStringCallback.allocate(cb, arena))
  extension (bytesCallBack:  Array[Byte] => Unit)
    def toBytesCallBack(
      using arena: Arena
    ): StringCallBack =
      val cb = new MlirStringCallback:
        def apply(message: MemorySegment, userData: MemorySegment): Unit =
          bytesCallBack(StringRef(message).toBytes)
      StringCallBack(MlirStringCallback.allocate(cb, arena))

  extension (stringCallBack: StringCallBack) def segment: MemorySegment = stringCallBack._segment
end given

given ContextApi with
  def createContext(
    using arena: Arena
  ): Context =
    Context(mlirContextCreate(arena))
  extension (context: Context)
    def destroy(): Unit          = mlirContextDestroy(context.segment)
    def loadDialect(
      dialectHandle: DialectHandle
    )(
      using arena:   Arena
    ): Unit = mlirDialectHandleLoadDialect(arena, dialectHandle.segment, context.segment)
    def segment:   MemorySegment = context._segment
    def sizeOf:    Int           = MlirContext.sizeof().toInt
end given

given DialectHandleApi with
  extension (dialectHandle: DialectHandle)
    def segment: MemorySegment = dialectHandle._segment
    def sizeOf:  Int           = MlirDialectHandle.sizeof().toInt
end given

given LocationApi with
  def unknownLocation(
    using arena: Arena,
    context:     Context
  ): Location = Location(mlirLocationUnknownGet(arena, context.segment))
  def fileLineColLocation(
    filename:    String,
    line:        Int,
    col:         Int
  )(
    using arena: Arena,
    context:     Context
  ): Location =
    Location(mlirLocationFileLineColGet(arena, context.segment, filename.toStringRef.segment, line, col))
  extension (location: Location)
    def segment: MemorySegment = location._segment
    def sizeOf:  Int           = MlirLocation.sizeof().toInt
    def getAttribute(
      using arena: Arena
    ): Attribute =
      Attribute(mlirLocationGetAttribute(arena, location.segment))
end given

given ModuleApi with
  def createModule(
    location:    Location
  )(
    using arena: Arena
  ): Module = new Module(mlirModuleCreateEmpty(arena, location.segment))

  extension (moduleString: String)
    def parseToModule(
      using arena: Arena,
      context:     Context
    ): Module = new Module(mlirModuleCreateParse(arena, context.segment, moduleString.toStringRef.segment))

  extension (module: Module)
    def segment:   MemorySegment = module._segment
    def sizeOf:    Int           = MlirModule.sizeof().toInt
    def getBody(
      using arena: Arena
    ) = Block(mlirModuleGetBody(arena, segment))
    def destroy(): Unit          = mlirModuleDestroy(module.segment)
    def getOperation(
      using arena: Arena
    ): Operation = Operation(mlirModuleGetOperation(arena, module.segment))
end given

given StringRefApi with
  extension (stringRef: StringRef)
    def segment:       MemorySegment = stringRef._segment
    def sizeOf:        Int           = MlirStringRef.sizeof().toInt
    def toBytes:       Array[Byte]   =
      MlirStringRef
        .data$get(stringRef.segment)
        .asSlice(0, MlirStringRef.length$get(stringRef.segment))
        .toArray(java.lang.foreign.ValueLayout.JAVA_BYTE)
    def toScalaString: String        = String(toBytes)

  extension (string: String)
    def toStringRef(
      using arena: Arena
    ): StringRef =
      val bytes  = string.getBytes()
      val buffer = arena.allocate(bytes.length + 1)
      buffer.copyFrom(MemorySegment.ofArray(bytes))
      StringRef(mlirStringRefCreateFromCString(arena, buffer))
end given

given OperationStateApi with
  extension (operationStateString: String)
    def toOperationState(
      location:    Location
    )(
      using arena: Arena
    ): OperationState =
      OperationState(mlirOperationStateGet(arena, operationStateString.toStringRef.segment, location.segment))
  extension (operationState:       OperationState)
    def segment:                     MemorySegment = operationState._segment
    def sizeOf:                      Int           = MlirOperationState.sizeof().toInt
    def addAttributes(
      attrs:       Seq[NamedAttribute]
    )(
      using arena: Arena
    ): Unit =
      val (ptr, length) = attrs.toMlirArray
      mlirOperationStateAddAttributes(operationState.segment, length, ptr)
    def addOperands(
      operands:    Seq[Value]
    )(
      using arena: Arena
    ): Unit =
      val (ptr, length) = operands.toMlirArray
      mlirOperationStateAddOperands(operationState.segment, length, ptr)
    def addResults(
      results:     Seq[Type]
    )(
      using arena: Arena
    ): Unit =
      val (ptr, length) = results.toMlirArray
      mlirOperationStateAddResults(operationState.segment, length, ptr)
    def addOwnedRegions(
      regions:     Seq[Region]
    )(
      using arena: Arena
    ): Unit =
      val (ptr, length) = regions.toMlirArray
      mlirOperationStateAddOwnedRegions(operationState.segment, length, ptr)
    def enableResultTypeInference(): Unit          =
      mlirOperationStateEnableResultTypeInference(operationState.segment)
end given

given OperationApi with
  extension (operationState: OperationState)
    def toOperation(
      using arena: Arena
    ): Operation =
      Operation(mlirOperationCreate(arena, operationState.segment))
  extension (operation:      Operation)
    def segment: MemorySegment = operation._segment
    def sizeOf:  Int           = MlirOperation.sizeof().toInt
    def getResult(
      i:           Int
    )(
      using arena: Arena
    ): Value =
      Value(mlirOperationGetResult(arena, operation.segment, i))
    def toModule(
      using arena: Arena
    ): Module = new Module(mlirModuleFromOperation(arena, operation.segment))
    def setInherentAttributeByName(
      name:        String,
      attribute:   Attribute
    )(
      using arena: Arena
    ): Unit =
      mlirOperationSetInherentAttributeByName(operation.segment, name.toStringRef.segment, attribute.segment)
    def getAttributeByName(
      name:        String
    )(
      using arena: Arena
    ): Attribute =
      Attribute(mlirOperationGetAttributeByName(arena, name.toStringRef.segment, operation.segment))
    def stringCallBack(
      callBack:    String => Unit
    )(
      using arena: Arena
    ): Unit =
      mlirOperationPrint(operation.segment, callBack.toStringCallBack.segment, MemorySegment.NULL)
    def bytecodeCallBack(
      callBack:    Array[Byte] => Unit
    )(
      using arena: Arena
    ): Unit =
      mlirOperationWriteBytecode(operation.segment, callBack.toBytesCallBack.segment, MemorySegment.NULL)
end given

given BlockApi with
  def createBlock(
    args:        Seq[Type],
    locs:        Seq[Location]
  )(
    using arena: Arena
  ): Block =
    Block(mlirBlockCreate(arena, args.length, args.toMlirArray._1, locs.toMlirArray._1))
  extension (block: Block)
    def segment: MemorySegment = block._segment
    def sizeOf:  Int           = MlirBlock.sizeof().toInt
    def getFirstOperation(
      using arena: Arena
    ): Operation = Operation(mlirBlockGetFirstOperation(arena, block.segment))
    def getArgument(
      i:           Int
    )(
      using arena: Arena
    ): Value =
      Value(mlirBlockGetArgument(arena, block.segment, i))
    def appendOwnedOperation(
      operation: Operation
    ): Unit =
      mlirBlockAppendOwnedOperation(block.segment, operation.segment)

    def insertOwnedOperationAfter(
      reference: Operation,
      operation: Operation
    ): Unit =
      mlirBlockInsertOwnedOperationAfter(block.segment, reference.segment, operation.segment)
    def insertOwnedOperationBefore(
      reference: Operation,
      operation: Operation
    ): Unit =
      mlirBlockInsertOwnedOperationBefore(block.segment, reference.segment, operation.segment)
end given

given IdentifierApi with
  extension (identifierString: String)
    def toIdentifier(
      using arena: Arena,
      context:     Context
    ): Identifier =
      Identifier(mlirIdentifierGet(arena, context._segment, identifierString.toStringRef.segment))
  extension (identifier:       Identifier)
    def segment: MemorySegment = identifier._segment
    def sizeOf:  Int           = MlirIdentifier.sizeof().toInt
end given

given NamedAttributeApi with
  extension (identifier:     Identifier)
    def toNamedAttribute(
      attr:        Attribute
    )(
      using arena: Arena
    ): NamedAttribute = NamedAttribute(mlirNamedAttributeGet(arena, identifier.segment, attr.segment))
  extension (namedAttribute: NamedAttribute)
    def segment: MemorySegment = namedAttribute._segment
    def sizeOf:  Int           = MlirNamedAttribute.sizeof().toInt
end given

given AttributeApi with
  def createUnitAttribute(
    using arena: Arena,
    context:     Context
  ): Attribute = Attribute(mlirUnitAttrGet(arena, context.segment))
  def allocateAttribute(
    using arena: Arena
  ): Attribute = Attribute(MlirAttribute.allocate(arena))
  extension (array:  Seq[Attribute])
    def toAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute =
      val (ptr, length) = array.toMlirArray
      Attribute(mlirArrayAttrGet(arena, context.segment, length, ptr))
  extension (tpe:    Type)
    def toAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute =
      Attribute(mlirTypeAttrGet(arena, tpe.segment))
  extension (bool:   Boolean)
    def toAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute =
      Attribute(mlirBoolAttrGet(arena, context.segment, if (bool) 1 else 0))
  extension (string: String)
    def toAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(mlirStringAttrGet(arena, context.segment, string.toStringRef.segment))
    def toSymbolRefAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(mlirFlatSymbolRefAttrGet(arena, context.segment, string.toStringRef.segment))

  extension (double: Double)
    def toAttribute(
      tpe:         Type
    )(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(mlirFloatAttrDoubleGet(arena, context.segment, tpe.segment, double))
  extension (int:    Long)
    def integerGet(
      tpe:         Type
    )(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(mlirIntegerAttrGet(arena, tpe.segment, int))

  extension (attribute: Attribute)
    def dump():      Unit          = mlirAttributeDump(attribute.segment)
    def segment:     MemorySegment = attribute._segment
    def sizeOf:      Int           = MlirAttribute.sizeof().toInt
    def numElements: Int           = mlirArrayAttrGetNumElements(attribute.segment).toInt
    def element(
      idx:         Int
    )(
      using arena: Arena
    ): Attribute = Attribute(mlirArrayAttrGetElement(arena, attribute.segment, idx.toLong))
    def getString(
      using arena: Arena
    ): String =
      StringRef(mlirStringAttrGetValue(arena, attribute.segment)).toScalaString
    def getInt:      Long          =
      mlirIntegerAttrGetValueInt(attribute.segment)
    def getSInt:     Long          =
      mlirIntegerAttrGetValueSInt(attribute.segment)
    def getUInt:     Long          =
      mlirIntegerAttrGetValueUInt(attribute.segment)
    def isInteger:   Boolean       =
      mlirAttributeIsAInteger(attribute.segment)
    def isString:    Boolean       =
      mlirAttributeIsAString(attribute.segment)
end given

given ValueApi with
  extension (value: Value)
    def tpe(
      using arena: Arena
    ): Type = Type(mlirValueGetType(arena, value.segment))
    def segment: MemorySegment = value._segment
    def sizeOf:  Int           = MlirValue.sizeof().toInt
end given

given TypeApi with
  def f64Type(
    using arena: Arena,
    context:     Context
  ): Type = Type(mlirF64TypeGet(arena, context.segment))
  def noneType(
    using arena: Arena,
    context:     Context
  ) = Type(mlirNoneTypeGet(arena, context.segment))
  extension (width: Int)
    def toSignedInteger(
      using arena: Arena,
      context:     Context
    ): Type = Type(mlirIntegerTypeSignedGet(arena, context.segment, width))
    def toUnsignedInteger(
      using arena: Arena,
      context:     Context
    ): Type = Type(mlirIntegerTypeUnsignedGet(arena, context.segment, width))
    def toIntegerType(
      using arena: Arena,
      context:     Context
    ): Type = Type(mlirIntegerTypeGet(arena, context.segment, width))
  extension (tpe:   Type)
    def segment: MemorySegment = tpe._segment
    def sizeOf:  Int           = MlirType.sizeof().toInt
end given

given RegionApi with
  def createRegion(
    using arena: Arena
  ): Region =
    Region(mlirRegionCreate(arena))
  extension (region: Region)
    def segment: MemorySegment = region._segment
    def sizeOf:  Int           = MlirRegion.sizeof().toInt
    def appendOwnedBlock(
      block: Block
    ): Unit = mlirRegionAppendOwnedBlock(region.segment, block.segment)
end given
