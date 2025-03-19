// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib

import java.lang.foreign.{Arena, MemorySegment}

// Structs
class AffineExpr(val _segment: MemorySegment)
trait AffineExprApi extends HasSegment[AffineExpr] with HasSizeOf[AffineExpr]

class AffineMap(val _segment: MemorySegment)
trait AffineMapApi extends HasSegment[AffineMap] with HasSizeOf[AffineMap]

class Diagnostic(val _segment: MemorySegment)
trait DiagnosticApi extends HasSegment[Diagnostic] with HasSizeOf[Diagnostic]

class TransformOptions(val _segment: MemorySegment)
trait TransformOptionsApi extends HasSegment[TransformOptions] with HasSizeOf[TransformOptions]

class ExecutionEngine(val _segment: MemorySegment)
trait ExecutionEngineApi extends HasSegment[ExecutionEngine] with HasSizeOf[ExecutionEngine]

class AsmState(val _segment: MemorySegment)
trait AsmStateApi extends HasSegment[AsmState] with HasSizeOf[AsmState]

class Attribute(val _segment: MemorySegment)
trait AttributeApi extends HasSegment[Attribute] with HasSizeOf[Attribute]:
  inline def allocateAttribute(
    using arena: Arena
  ): Attribute
  inline def getNull(
    using arena: Arena,
    context:     Context
  ): Attribute
  // Location
  extension (attribute: Attribute) inline def isLocation: Boolean
  // Array
  inline def arrayAttrGetTypeID(
    using arena: Arena
  ): TypeID
  extension (array:     Seq[Attribute])
    inline def arrayAttrGet(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (attribute: Attribute)
    inline def isArray:                 Boolean
    inline def arrayAttrGetNumElements: Int
    inline def arrayAttrGetElement(
      idx:         Int
    )(
      using arena: Arena
    ):                                  Attribute
  // Dictionary
  inline def dictionaryAttrGetTypeID(
    using arena: Arena
  ): TypeID
  extension (map:       Map[String, Attribute])
    inline def directoryAttrGet(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (attribute: Attribute)
    inline def isDictionary:                 Boolean
    inline def dictionaryAttrGetNumElements: Int
    inline def dictionaryAttrGetElement(
      idx:         Int
    )(
      using arena: Arena
    ):                                       Attribute
  // Floating point
  inline def floatAttrGetTypeID(
    using arena: Arena
  ): TypeID
  extension (double:    Double)
    inline def floatAttrDoubleGet(
      tpe:         Type
    )(
      using arena: Arena,
      context:     Context
    ): Attribute
    inline def floatAttrDoubleGetChecked(
      tpe:         Type
    )(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (attribute: Attribute)
    inline def isFloat:                 Boolean
    inline def floatAttrGetValueDouble: Double
  // Integer
  inline def integerAttrGetTypeID(
    using arena: Arena
  ): TypeID
  extension (int:       Long)
    inline def integerAttrGet(
      tpe:         Type
    )(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (attribute: Attribute)
    inline def isInteger:               Boolean
    inline def integerAttrGetValueInt:  Long
    inline def integerAttrGetValueSInt: Long
    inline def integerAttrGetValueUInt: Long
  // Bool
  extension (bool:      Boolean)
    inline def boolAttrGet(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (attribute: Attribute)
    inline def isBool:           Boolean
    inline def boolAttrGetValue: Boolean

  // String
  def stringAttrGetTypeID(
    using arena: Arena
  ): TypeID

  extension (string:    String)
    inline def stringAttrGet(
      using arena: Arena,
      context:     Context
    ): Attribute
    inline def stringAttrTypedGet(
      tpe:         Type
    )(
      using arena: Arena
    ): Attribute
  extension (attribute: Attribute)
    inline def isString: Boolean
    inline def stringAttrGetValue(
      using arena: Arena
    ):                   String
  // SymbolRef
  inline def symbolRefAttrGetTypeID(
    using arena: Arena
  ): TypeID

  extension (symbol:    String)
    inline def symbolRefAttrGet(
      references:  Seq[Attribute]
    )(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (attribute: Attribute)
    inline def isSymbolRef:                         Boolean
    inline def symbolRefAttrGetRootReference(
      using arena: Arena
    ):                                              String
    inline def symbolRefAttrGetLeafReference(
      using arena: Arena
    ):                                              String
    inline def symbolRefAttrGetNumNestedReferences: Long
    inline def symbolRefAttrGetNestedReference(
      pos:         Long
    )(
      using arena: Arena
    ):                                              Attribute
    inline def disctinctAttrCreate(
      using arena: Arena
    ):                                              Attribute
  // Flat SymbolRef
  extension (string:    String)
    inline def flatSymbolRefAttrGet(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (attribute: Attribute)
    inline def isFlatSymbolRef: Boolean
    inline def flatSymbolRefAttrGetValue(
      using arena: Arena
    ):                          String

  // Type
  inline def typeAttrGetTypeID(
    using arena: Arena
  ): TypeID

  extension (tpe:       Type)
    inline def typeAttrGet(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (attribute: Attribute)
    inline def isType: Boolean
    inline def typeAttrGetValue(
      using arena: Arena
    ):                 Type

  // Unit
  inline def unitAttrGetTypeID(
    using arena: Arena
  ): TypeID

  inline def unitAttrGet(
    using arena: Arena,
    context:     Context
  ): Attribute

  extension (attribute: Attribute) inline def isUnit: Boolean

  inline def denseArrayAttrGetTypeID(
    using arena: Arena
  ): TypeID

  extension (bools:     Seq[Boolean])
    inline def denseBoolArrayGet(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (ints:      Seq[Int])
    inline def denseI8ArrayGet(
      using arena: Arena,
      context:     Context
    ): Attribute
    inline def denseI16ArrayGet(
      using arena: Arena,
      context:     Context
    ): Attribute
    inline def denseI32ArrayGet(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (longs:     Seq[Long])
    inline def denseI64ArrayGet(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (floats:    Seq[Float])
    inline def denseF32ArrayGet(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (doubles:   Seq[Double])
    inline def denseF64ArrayGet(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (attribute: Attribute)
    inline def isDenseBoolArray:         Boolean
    inline def isDenseI8Array:           Boolean
    inline def isDenseI16Array:          Boolean
    inline def isDenseI32Array:          Boolean
    inline def isDenseI64Array:          Boolean
    inline def isDenseF32Array:          Boolean
    inline def isDenseF64Array:          Boolean
    inline def denseArrayGetNumElements: Long
    inline def denseBoolArrayGetElement(pos: Long): Boolean
    inline def denseI8ArrayGetElement(pos:   Long): Int
    inline def denseI16ArrayGetElement(pos:  Long): Int
    inline def denseI32ArrayGetElement(pos:  Long): Int
    inline def denseI64ArrayGetElement(pos:  Long): Long
    inline def denseF32ArrayGetElement(pos:  Long): Float
    inline def denseF64ArrayGetElement(pos:  Long): Double
end AttributeApi

class Block(val _segment: MemorySegment)
trait BlockApi extends HasSegment[Block] with HasSizeOf[Block]:
  inline def blockCreate(
    args:        Seq[Type],
    locs:        Seq[Location]
  )(
    using arena: Arena
  ): Block
  extension (block: Block)
    inline def getParentOperation(
      using arena: Arena
    ):                    Operation
    inline def getNextInRegion(
      using arena: Arena
    ):                    Block
    inline def getFirstOperation(
      using arena: Arena
    ):                    Operation
    inline def getTerminator(
      using arena: Arena
    ):                    Operation
    inline def addArgument(
      tpe:         Type,
      loc:         Location
    )(
      using arena: Arena
    ):                    Operation
    inline def insertArgument(
      pos:         Int,
      tpe:         Type,
      loc:         Location
    )(
      using arena: Arena
    ):                    Operation
    inline def getArgument(
      pos:         Long
    )(
      using arena: Arena
    ):                    Value
    inline def argumentGetOwner(
      using arena: Arena
    ):                    Block
    inline def destroy(): Unit
    inline def detach():  Unit
    inline def appendOwnedOperation(operation:       Operation): Unit
    inline def insertOwnedOperation(pos:             Long, operation:      Operation): Unit
    inline def insertOwnedOperationAfter(reference:  Operation, operation: Operation): Unit
    inline def insertOwnedOperationBefore(reference: Operation, operation: Operation): Unit
    inline def eraseArgument(index:                  Int): Unit
    inline def print(
      callBack:    String => Unit
    )(
      using arena: Arena
    ): Unit
end BlockApi

class BytecodeWriterConfig(val _segment: MemorySegment)
trait BytecodeWriterConfigApi extends HasSegment[BytecodeWriterConfig] with HasSizeOf[BytecodeWriterConfig]

class Context(val _segment: MemorySegment)
trait ContextApi extends HasSegment[Context] with HasSizeOf[Context]:
  inline def contextCreate(
    using arena: Arena
  ): Context
  inline def contextCreateWithThreading(
    threadingEnabled: Boolean
  )(
    using arena:      Arena
  ): Context
  inline def contextCreateWithRegistry(
    registry:         DialectRegistry,
    threadingEnabled: Boolean
  )(
    using arena:      Arena
  ): Context
  extension (context: Context)
    inline def getOrLoadDialect(
      name:        String
    )(
      using arena: Arena
    ):                    Dialect
    inline def destroy(): Unit
    inline def allowUnregisteredDialects(allow: Boolean):         Unit
    inline def appendDialectRegistry(registry:  DialectRegistry): Unit
    inline def enableMultithreading(enable:     Boolean):         Unit
    inline def loadAllAvailableDialects(): Unit
    inline def setThreadPool(threadPool: LlvmThreadPool): Unit
end ContextApi

class Dialect(val _segment: MemorySegment)
trait DialectApi extends HasSegment[Dialect] with HasSizeOf[Dialect]

class DialectHandle(val _segment: MemorySegment)
trait DialectHandleApi extends HasSegment[DialectHandle] with HasSizeOf[DialectHandle]:
  extension (dialectHandle: DialectHandle)
    inline def getNamespace(
      using arena: Arena
    ): String
    inline def loadDialect(
      using arena: Arena,
      context:     Context
    ): Unit
    inline def insertDialect(dialectRegistry: DialectRegistry): Unit
    inline def insertDialect(
    )(
      using context: Context
    ): Unit
  extension (context:       Context)
    inline def loadFuncDialect(
    )(
      using arena: Arena
    ): Unit
end DialectHandleApi

class DialectRegistry(val _segment: MemorySegment)
trait DialectRegistryApi extends HasSegment[DialectRegistry] with HasSizeOf[DialectRegistry]:
  inline def registryCreate(
  )(
    using arena: Arena
  ): DialectRegistry
  extension (dialectRegistry: DialectRegistry) inline def destroy(): Unit
end DialectRegistryApi

class Identifier(val _segment: MemorySegment)
trait IdentifierApi extends HasSegment[Identifier] with HasSizeOf[Identifier]:
  extension (identifierString: String)
    inline def identifierGet(
      using arena: Arena,
      context:     Context
    ): Identifier
  extension (identifier:       Identifier)
    inline def getContext(
      using arena: Arena
    ): Context
    inline def str(
      using arena: Arena
    ): String
end IdentifierApi

class Location(val _segment: MemorySegment)
trait LocationApi extends HasSegment[Location] with HasSizeOf[Location]:
  inline def locationFromAttribute(
    attribute: Attribute
  )(arena:     Arena
  ): Location
  inline def locationFileLineColGet(
    filename:    String,
    line:        Int,
    col:         Int
  )(
    using arena: Arena,
    context:     Context
  ): Location
  inline def locationCallSiteGet(
    callee:      Location,
    caller:      Location
  )(
    using arena: Arena,
    context:     Context
  ): Location
  inline def locationFusedGet(
    locations:   Seq[Location],
    metadata:    Attribute
  )(
    using arena: Arena,
    context:     Context
  ): Location
  inline def locationNameGet(
    name:        String,
    childLoc:    Location
  )(
    using arena: Arena,
    context:     Context
  ): Location
  inline def locationUnknownGet(
    using arena: Arena,
    context:     Context
  ): Location
  extension (location: Location)
    inline def getAttribute(
      using arena: Arena
    ): Attribute
    inline def locationGetContext(
      using arena: Arena
    ): Context
end LocationApi

class Module(val _segment: MemorySegment)
trait ModuleApi extends HasSegment[Module] with HasSizeOf[Module]:
  inline def moduleCreateEmpty(
    location:    Location
  )(
    using arena: Arena
  ): Module
  inline def moduleCreateParse(
    module:      String | Array[Byte]
  )(
    using arena: Arena,
    context:     Context
  ): Module
  inline def moduleFromOperation(
    op:          Operation
  )(
    using arena: Arena
  ): Module
  extension (module: Module)
    inline def getContext(
      using arena: Arena
    ):                    Context
    inline def getBody(
      using arena: Arena
    ):                    Block
    inline def getOperation(
      using arena: Arena
    ):                    Operation
    inline def destroy(): Unit
end ModuleApi

class NamedAttribute(val _segment: MemorySegment)
trait NamedAttributeApi extends HasSegment[NamedAttribute] with HasSizeOf[NamedAttribute]:
  inline def namedAttributeGet(
    identifier:  Identifier,
    attribute:   Attribute
  )(
    using arena: Arena
  ): NamedAttribute
end NamedAttributeApi

class OpOperand(val _segment: MemorySegment)
trait OpOperandApi extends HasSegment[OpOperand] with HasSizeOf[OpOperand]

class OpPrintingFlags(val _segment: MemorySegment)
trait OpPrintingFlagsApi extends HasSegment[OpPrintingFlags] with HasSizeOf[OpPrintingFlags]:
  inline def opPrintingFlagsCreate(
  )(
    using arena: Arena
  ): OpPrintingFlags

  extension (opPrintingFlags: OpPrintingFlags)
    inline def flagsDestroy(): Unit
    inline def flagsElideLargeElementsAttrs(largeElementLimit:   Long): Unit
    inline def flagsElideLargeResourceString(largeResourceLimit: Long): Unit
    inline def flagsEnableDebugInfo(enable:                      Boolean, prettyForm: Boolean): Unit
    inline def flagsPrintGenericOpForm(): Unit
    inline def flagsUseLocalScope():      Unit
    inline def flagsAssumeVerified():     Unit
    inline def flagsSkipRegions():        Unit
end OpPrintingFlagsApi

class Operation(val _segment: MemorySegment)
trait OperationApi extends HasSegment[Operation] with HasSizeOf[Operation]:
  inline def operationCreate(
    state:       OperationState
  )(
    using arena: Arena
  ): Operation
  inline def operationCreate(
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
  ): Operation
  inline def operationCreateParse(
    sourceStr:   String,
    sourceName:  String
  )(
    using arena: Arena,
    context:     Context
  ): Operation
  inline def operationClone(
    op:          Operation
  )(
    using arena: Arena
  ): Operation
  extension (operation: Operation)
    inline def getContext(
      using arena: Arena
    ):                             Context
    inline def getLocation(
      using arena: Arena
    ):                             Location
    inline def getTypeID(
      using arena: Arena
    ):                             TypeID
    inline def getName(
      using arena: Arena
    ):                             Identifier
    inline def getBlock(
      using arena: Arena
    ):                             Block
    inline def getParentOperation(
      using arena: Arena
    ):                             Operation
    inline def getRegion(
      pos:         Long
    )(
      using arena: Arena
    ):                             Region
    inline def getNextInBlock(
      using arena: Arena
    ):                             Operation
    inline def getOperand(
      pos:         Long
    )(
      using arena: Arena
    ):                             Value
    inline def getResult(
      pos:         Long
    )(
      using arena: Arena
    ):                             Value
    inline def getNumResults:      Long
    inline def getSuccessor(
      pos:         Long
    )(
      using arena: Arena
    ):                             Block
    inline def getInherentAttributeByName(
      name:        String
    )(
      using arena: Arena
    ):                             Attribute
    inline def getDiscardableAttribute(
      pos:         Long
    )(
      using arena: Arena
    ):                             NamedAttribute
    inline def getDiscardableAttributeByName(
      name:        String
    )(
      using arena: Arena
    ):                             Attribute
    inline def getAttribute(
      pos:         Long
    )(
      using arena: Arena
    ):                             NamedAttribute
    inline def getAttributeByName(
      name:        String
    )(
      using arena: Arena
    ):                             Attribute
    inline def writeBytecodeWithConfig(
      config:      BytecodeWriterConfig,
      callback:    Array[Byte] => Unit
    )(
      using arena: Arena
    ):                             LogicalResult
    inline def getFirstRegion(
      using arena: Arena
    ):                             Region
    inline def destroy():          Unit
    inline def removeFromParent(): Unit
    inline def setOperand(pos:   Long, newValue: Value): Unit
    inline def setOperands(
      operands: Seq[Value]
    )(
      using Arena
    ): Unit
    inline def setSuccessor(pos: Long, block:    Block): Unit
    inline def setInherentAttributeByName(
      name: String,
      attr: Attribute
    )(
      using Arena
    ): Unit
    inline def setDiscardableAttributeByName(
      name: String,
      attr: Attribute
    )(
      using Arena
    ): Unit
    inline def setAttributeByName(
      name: String,
      attr: Attribute
    )(
      using Arena
    ): Unit
    inline def print(
      callback: String => Unit
    )(
      using Arena
    ): Unit
    inline def printWithFlags(
      callback: String => Unit
    )(
      using Arena
    ): Unit
    inline def printWithState(
      asmState: AsmState,
      callback: String => Unit
    )(
      using Arena
    ): Unit
    inline def writeBytecode(
      callBack:    Array[Byte] => Unit
    )(
      using arena: Arena
    ): Unit
    inline def dump(): Unit
    inline def moveAfter(other:  Operation): Unit
    inline def moveBefore(other: Operation): Unit
    inline def walk(
      callback:    Operation => WalkResultEnum,
      walk:        WalkEnum
    )(
      using arena: Arena
    ): Unit

    inline def appendToBlock(
    )(
      using block: Block
    ): Unit
    inline def insertToBlock(
      pos:         Long
    )(
      using block: Block
    ): Unit
    inline def insertAfter(
      ref:         Operation
    )(
      using block: Block
    ): Unit
    inline def insertBefore(
      ref:         Operation
    )(
      using block: Block
    ): Unit
end OperationApi

class OperationState(val _segment: MemorySegment)
trait OperationStateApi extends HasSegment[OperationState] with HasSizeOf[OperationState]:
  inline def operationStateGet(
    name:        String,
    loc:         Location
  )(
    using arena: Arena
  ): OperationState
  extension (operationState: OperationState)
    inline def addResults(
      results:     Seq[Type]
    )(
      using arena: Arena
    ):                                      Unit
    inline def addOperands(
      operands:    Seq[Value]
    )(
      using arena: Arena
    ):                                      Unit
    inline def addOwnedRegions(
      regions:     Seq[Region]
    )(
      using arena: Arena
    ):                                      Unit
    inline def addSuccessors(
      blocks:      Seq[Block]
    )(
      using arena: Arena
    ):                                      Unit
    inline def addAttributes(
      attrs:       Seq[NamedAttribute]
    )(
      using arena: Arena
    ):                                      Unit
    inline def enableResultTypeInference(): Unit
end OperationStateApi

class Region(val _segment: MemorySegment)
trait RegionApi extends HasSegment[Region] with HasSizeOf[Region]:
  inline def regionCreate(
    using arena: Arena
  ): Region
  extension (op: Region)
    inline def getFirstBlock(
      using arena: Arena
    ): Block
    inline def getNextInOperation(
      using arena: Arena
    ): Region
    inline def destroy(
    )(
      using arena: Arena
    ): Unit
    inline def appendOwnedBlock(
      block: Block
    ): Unit
    inline def insertOwnedBlock(pos:             Long, block:  Block): Unit
    inline def insertOwnedBlockAfter(reference:  Block, block: Block): Unit
    inline def insertOwnedBlockBefore(reference: Block, block: Block): Unit
end RegionApi

class SymbolTable(val _segment: MemorySegment)
trait SymbolTableApi extends HasSegment[SymbolTable] with HasSizeOf[SymbolTable]

class Type(val _segment: MemorySegment)
trait TypeApi extends HasSegment[Type] with HasSizeOf[Type]:
  inline def f64TypeGet(
    using arena: Arena,
    context:     Context
  ): Type

  inline def noneTypeGet(
    using arena: Arena,
    context:     Context
  ): Type

  extension (width: Int)
    inline def integerTypeSignedGet(
      using arena: Arena,
      context:     Context
    ): Type
    inline def integerTypeUnsignedGet(
      using arena: Arena,
      context:     Context
    ): Type
    inline def integerTypeGet(
      using arena: Arena,
      context:     Context
    ): Type
end TypeApi

class Value(val _segment: MemorySegment)
trait ValueApi extends HasSegment[Value] with HasSizeOf[Value]:
  extension (value: Value)
    inline def getType(
      using arena: Arena
    ): Type
    inline def getFirstUse(
      using arena: Arena
    ): Type
    inline def setType(tpe: Type): Unit
    inline def dump(): Unit
    inline def print(
      callback:    String => Unit
    )(
      using arena: Arena
    ):                 Unit
    inline def printAsOperand(
      state:       AsmState,
      callback:    String => Unit
    )(
      using arena: Arena
    ):                 Unit
    inline def replaceAllUsesOfWith(w: Value): Unit
end ValueApi

class IntegerSet(val _segment: MemorySegment)
trait IntegerSetApi extends HasSegment[IntegerSet] with HasSizeOf[IntegerSet]

class ExternalPass(val _segment: MemorySegment)
trait ExternalPassApi extends HasSegment[ExternalPass] with HasSizeOf[ExternalPass]

class ExternalPassCallbacks(val _segment: MemorySegment)
trait ExternalPassCallbacksApi extends HasSegment[ExternalPassCallbacks] with HasSizeOf[ExternalPassCallbacks]

class OpPassManager(val _segment: MemorySegment)

trait OpPassManagerApi extends HasSegment[OpPassManager] with HasSizeOf[OpPassManager]:
  extension (opPassManager: OpPassManager)
    inline def getNestedUnder(
      passManager:   PassManager,
      operationName: String
    )(
      using arena:   Arena
    ): OpPassManager
    inline def addPipeline(
      pipelineElements: String,
      callback:         String => Unit
    )(
      using arena:      Arena
    ): LogicalResult
    inline def parsePassPipeline(
      pipeline:    String,
      callback:    String => Unit
    )(
      using arena: Arena
    ): LogicalResult
    inline def addOwnedPass(
      pass: Pass
    ): Unit
end OpPassManagerApi

class Pass(val _segment: MemorySegment)
trait PassApi extends HasSegment[Pass] with HasSizeOf[Pass]:
  inline def createExternalPass(
    passId:            TypeID,
    name:              String,
    argument:          String,
    description:       String,
    opName:            String,
    dependentDialects: Seq[DialectHandle],
    callbacks:         ExternalPassCallbacks
  )(
    using arena:       Arena
  ): Pass

end PassApi

class PassManager(val _segment: MemorySegment)
trait PassManagerApi extends HasSegment[PassManager] with HasSizeOf[PassManager]:
  inline def passManagerCreate(
    using arena: Arena,
    context:     Context
  ): PassManager

  inline def passManagerCreateOnOperation(
    name:        String
  )(
    using arena: Arena,
    context:     Context
  ): PassManager

  extension (passManager: PassManager)
    inline def getAsOpPassManager(
      using arena: Arena
    ):                    OpPassManager
    inline def runOnOp(
      operation:   Operation
    )(
      using arena: Arena
    ):                    LogicalResult
    inline def getNestedUnder(
      operationName: String
    )(
      using arena:   Arena
    ):                    OpPassManager
    inline def destroy(): Unit
    inline def enableIRPrinting(
      printBeforeAll:          Boolean,
      printAfterAll:           Boolean,
      printModuleScope:        Boolean,
      printAfterOnlyOnChange:  Boolean,
      printAfterOnlyOnFailure: Boolean,
      flags:                   OpPrintingFlags,
      treePrintingPath:        String
    )(
      using arena:             Arena
    ):                    Unit
    inline def enableVerifier(enable: Boolean): Unit
    inline def addOwnedPass(
      pass: Pass
    ): Unit

end PassManagerApi

class FrozenRewritePatternSet(val _segment: MemorySegment)
trait FrozenRewritePatternSetApi extends HasSegment[FrozenRewritePatternSet] with HasSizeOf[FrozenRewritePatternSet]

class GreedyRewriteDriverConfig(val _segment: MemorySegment)
trait GreedyRewriteDriverConfigApi
    extends HasSegment[GreedyRewriteDriverConfig]
    with HasSizeOf[GreedyRewriteDriverConfig]

class PDLPatternModule(val _segment: MemorySegment)
trait PDLPatternModuleApi extends HasSegment[PDLPatternModule] with HasSizeOf[PDLPatternModule]

class RewritePatternSet(val _segment: MemorySegment)
trait RewritePatternSetApi extends HasSegment[RewritePatternSet] with HasSizeOf[RewritePatternSet]

class RewriterBase(val _segment: MemorySegment)
trait RewriterBaseApi extends HasSegment[RewriterBase] with HasSizeOf[RewriterBase]

class LlvmThreadPool(val _segment: MemorySegment)
trait LlvmThreadPoolApi extends HasSegment[LlvmThreadPool] with HasSizeOf[LlvmThreadPool]:
  inline def llvmThreadPoolCreate(
  )(
    using arena: Arena
  ): LlvmThreadPool
  extension (llvmThreadPool: LlvmThreadPool) inline def destroy(): Unit
end LlvmThreadPoolApi

class LogicalResult(val _segment: MemorySegment)
trait LogicalResultApi extends HasSegment[LogicalResult] with HasSizeOf[LogicalResult]

class StringRef(val _segment: MemorySegment)
trait StringRefApi extends HasSegment[StringRef] with HasSizeOf[StringRef]:
  extension (string:    String)
    inline def toStringRef(
      using arena: Arena
    ): StringRef
  extension (stringRef: StringRef)
    inline def toBytes:       Array[Byte]
    inline def toScalaString: String
end StringRefApi

class TypeID(val _segment: MemorySegment)
trait TypeIDApi extends HasSegment[TypeID] with HasSizeOf[TypeID]

class TypeIDAllocator(val _segment: MemorySegment)
trait TypeIDAllocatorApi extends HasSegment[TypeIDAllocator] with HasSizeOf[TypeIDAllocator]

class DiagnosticHandler(val _segment: MemorySegment)
trait DiagnosticHandlerApi extends HasSegment[DiagnosticHandler]

class DiagnosticHandlerID(val _segment: MemorySegment)
trait DiagnosticHandlerIDApi extends HasSegment[DiagnosticHandlerID]

class SparseTensorLevelType(val _segment: MemorySegment)
trait SparseTensorLevelTypeApi extends HasSegment[SparseTensorLevelType]

class OperationWalkCallback(val _segment: MemorySegment)
trait OperationWalkCallbackApi extends HasSegment[OperationWalkCallback]

class ShapedTypeComponentsCallback(val _segment: MemorySegment)
trait ShapedTypeComponentsCallbackApi extends HasSegment[ShapedTypeComponentsCallback]

class TypesCallback(val _segment: MemorySegment)
trait TypesCallbackApi extends HasSegment[TypesCallback]

class StringCallback(val _segment: MemorySegment)
trait StringCallbackApi extends HasSegment[StringCallback]:
  extension (stringCallBack: String => Unit)
    inline def stringToStringCallback(
      using arena: Arena
    ): StringCallback
  extension (bytesCallBack:  Array[Byte] => Unit)
    inline def bytesToStringCallback(
      using arena: Arena
    ): StringCallback
end StringCallbackApi

enum DiagnosticSeverityEnum:
  case Error
  case Note
  case Remark
  case Warning
end DiagnosticSeverityEnum
trait DiagnosticEnumApi extends HasSizeOf[DiagnosticSeverityEnum] with EnumHasToNative[DiagnosticSeverityEnum]

enum WalkEnum:
  case PostOrder
  case PreOrder
end WalkEnum
trait WalkEnumApi extends HasSizeOf[WalkEnum] with EnumHasToNative[WalkEnum]

enum WalkResultEnum:
  case Advance
  case Interrupt
  case Skip
end WalkResultEnum
trait WalkResultEnumApi extends HasSizeOf[WalkResultEnum] with EnumHasToNative[WalkResultEnum]

// Scala Support Traits
trait ScalaTpeToMlirArray[T <: Int | Long | Float | Double]:
  extension (xs: Seq[T])
    inline def toMlirArray(
      using arena: Arena
    ): MemorySegment

trait ToMlirArray[E]:
  extension (xs: Seq[E])
    inline def toMlirArray(
      using arena: Arena,
      api:         HasSizeOf[E] & (HasSegment[E] | EnumHasToNative[E])
    ): MemorySegment

trait HasSegment[T]:
  extension (ref: T) inline def segment: MemorySegment
end HasSegment

trait HasSizeOf[T]:
  extension (ref: T) inline def sizeOf: Int
end HasSizeOf

trait EnumHasToNative[T]:
  extension (int: Int) inline def fromNative: T
  extension (ref: T) inline def toNative:     Int
end EnumHasToNative

trait HasOperation[T]:
  extension (ref: T) def operation: Operation
end HasOperation
