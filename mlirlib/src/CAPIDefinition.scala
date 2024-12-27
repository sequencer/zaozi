// SPDX-License-Identifier: Apache-2.0
package org.llvm.mlir.scalalib

import java.lang.foreign.{Arena, MemorySegment}
import scala.collection.mutable.ArrayBuffer

class Context(
  val _segment: MemorySegment)

class Module(
  val _segment: MemorySegment)

class Region(
  val _segment: MemorySegment):
  // No C-API to get the index i of Region.
  val _blocks: ArrayBuffer[Block] = scala.collection.mutable.ArrayBuffer[Block]()
end Region

class Block(
  val _segment: MemorySegment)

class Location(
  val _segment: MemorySegment)

class Attribute(
  val _segment: MemorySegment)

class NamedAttribute(
  val _segment: MemorySegment)

class Value(
  val _segment: MemorySegment)

class Type(
  val _segment: MemorySegment)

class OperationState(
  val _segment: MemorySegment)

class Operation(
  val _segment: MemorySegment)

class Identifier(
  val _segment: MemorySegment)

class StringRef(
  val _segment: MemorySegment)

class DialectHandle(
  val _segment: MemorySegment)

class StringCallBack(
  val _segment: MemorySegment)

trait ToMlirArray[E]:
  extension (xs: Seq[E])
    inline def toMlirArray(
      using arena: Arena,
      api:         HasSizeOf[E] & (HasSegment[E] | EnumHasToNative[E])
    ): (MemorySegment, Int)

trait HasSegment[T]:
  extension (ref: T) def segment: MemorySegment
end HasSegment

trait HasSizeOf[T]:
  extension (ref: T) def sizeOf: Int
end HasSizeOf

trait EnumHasToNative[T]:
  extension (ref: T) def toNative: Int
end EnumHasToNative

// C-API Definitions
trait DialectHandleApi extends HasSegment[DialectHandle] with HasSizeOf[DialectHandle]:

end DialectHandleApi

trait ValueApi extends HasSegment[Value] with HasSizeOf[Value]:
  extension (value: Value)
    def tpe(
      using arena: Arena
    ): Type
end ValueApi

trait ContextApi extends HasSegment[Context] with HasSizeOf[Context]:
  def createContext(
    using arena: Arena
  ): Context
  extension (context: Context) def destroy(): Unit
end ContextApi

trait ModuleApi extends HasSegment[Module] with HasSizeOf[Module]:
  def createModule(
    location:    Location
  )(
    using arena: Arena
  ): Module
  extension (moduleString: String)
    def parseToModule(
      using arena: Arena,
      context:     Context
    ): Module
  extension (module:       Module)
    def getBody(
      using arena: Arena
    ):             Block
    def destroy(): Unit
    def getOperation(
      using arena: Arena
    ):             Operation
end ModuleApi

trait RegionApi extends HasSegment[Region] with HasSizeOf[Region]:
  def createRegion(
    using arena: Arena
  ): Region
  extension (op: Region)
    def block(idx: Int): Block
    def appendOwnedBlock(
      block: Block
    ): Unit
end RegionApi

trait BlockApi extends HasSegment[Block] with HasSizeOf[Block]:
  def createBlock(
    args:        Seq[Type],
    locs:        Seq[Location]
  )(
    using arena: Arena
  ): Block

  extension (block: Block)
    def getFirstOperation(
      using arena: Arena
    ): Operation
    def getArgument(
      i:           Int
    )(
      using arena: Arena
    ): Value
    def appendOwnedOperation(
      operation: Operation
    ): Unit
    def insertOwnedOperationAfter(
      reference: Operation,
      operation: Operation
    ): Unit
    def insertOwnedOperationBefore(
      reference: Operation,
      operation: Operation
    ): Unit
end BlockApi

trait LocationApi extends HasSegment[Location] with HasSizeOf[Location]:
  def unknownLocation(
    using arena: Arena,
    context:     Context
  ): Location
  def fileLineColLocation(
    filename:    String,
    line:        Int,
    col:         Int
  )(
    using arena: Arena,
    context:     Context
  ): Location
  extension (location: Location)
    def getAttribute(
      using arena: Arena
    ): Attribute
end LocationApi

trait OperationStateApi extends HasSegment[OperationState] with HasSizeOf[OperationState]:
  extension (operationStateString: String)
    def toOperationState(
      location:    Location
    )(
      using arena: Arena
    ): OperationState
  extension (operationState:       OperationState)
    def addAttributes(
      attrs:       Seq[NamedAttribute]
    )(
      using arena: Arena
    ):                               Unit
    def addOperands(
      operands:    Seq[Value]
    )(
      using arena: Arena
    ):                               Unit
    def addResults(
      results:     Seq[Type]
    )(
      using arena: Arena
    ):                               Unit
    def addOwnedRegions(
      regions:     Seq[Region]
    )(
      using arena: Arena
    ):                               Unit
    def enableResultTypeInference(): Unit
end OperationStateApi

trait OperationApi extends HasSegment[Operation] with HasSizeOf[Operation]:
  extension (operationState: OperationState)
    def toOperation(
      using arena: Arena
    ): Operation
  extension (operation:      Operation)
    def getResult(
      i:           Int
    )(
      using arena: Arena
    ): Value
    def toModule(
      using arena: Arena
    ): Module
    def setInherentAttributeByName(
      name:        String,
      attribute:   Attribute
    )(
      using arena: Arena
    ): Unit
    def getAttributeByName(
      name:        String
    )(
      using arena: Arena
    ): Attribute
    def stringCallBack(
      callBack:    String => Unit
    )(
      using arena: Arena
    ): Unit
    def bytecodeCallBack(
      callBack:    Array[Byte] => Unit
    )(
      using arena: Arena
    ): Unit
end OperationApi

trait IdentifierApi extends HasSegment[Identifier] with HasSizeOf[Identifier]:
  extension (identifierString: String)
    def toIdentifier(
      using arena: Arena,
      context:     Context
    ): Identifier
end IdentifierApi

trait TypeApi extends HasSegment[Type] with HasSizeOf[Type]:
  def f64Type(
    using arena: Arena,
    context:     Context
  ): Type
  def noneType(
    using arena: Arena,
    context:     Context
  ): Type
  extension (width: Int)
    def toSignedInteger(
      using arena: Arena,
      context:     Context
    ): Type
    def toUnsignedInteger(
      using arena: Arena,
      context:     Context
    ): Type
    def toIntegerType(
      using arena: Arena,
      context:     Context
    ): Type
end TypeApi

trait NamedAttributeApi extends HasSegment[NamedAttribute] with HasSizeOf[NamedAttribute]:
  extension (identifier: Identifier)
    def toNamedAttribute(
      attr:        Attribute
    )(
      using arena: Arena
    ): NamedAttribute
end NamedAttributeApi

trait AttributeApi extends HasSegment[Attribute] with HasSizeOf[Attribute]:
  def createUnitAttribute(
    using arena: Arena,
    context:     Context
  ): Attribute
  def allocateAttribute(
    using arena: Arena
  ): Attribute
  extension (array:     Seq[Attribute])
    def toAttributeArrayAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (tpe:       Type)
    def toTypeAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (bool:      Boolean)
    def toBooleanAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (string:    String)
    def toStringAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute
    def toSymbolRefAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (double:    Double)
    def toDoubleAttribute(
      tpe:         Type
    )(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (int:       Long)
    def toIntegerAttribute(
      tpe:         Type
    )(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (attribute: Attribute)
    def dump():      Unit
    def numElements: Int
    def element(
      idx:         Int
    )(
      using arena: Arena
    ):               Attribute
    def getString(
      using arena: Arena
    ):               String
    def getInt:      Long
    def getSInt:     Long
    def getUInt:     Long
    def isInteger:   Boolean
    def isString:    Boolean
end AttributeApi

trait StringRefApi extends HasSegment[StringRef] with HasSizeOf[StringRef]:
  extension (string:    String)
    def toStringRef(
      using arena: Arena
    ): StringRef
  extension (stringRef: StringRef)
    def toBytes:       Array[Byte]
    def toScalaString: String
end StringRefApi

trait StringCallBackApi extends HasSegment[StringCallBack]:
  extension (stringCallBack: String => Unit)
    def toStringCallBack(
      using arena: Arena
    ): StringCallBack
  extension (bytesCallBack:  Array[Byte] => Unit)
    def toBytesCallBack(
      using arena: Arena
    ): StringCallBack
end StringCallBackApi
