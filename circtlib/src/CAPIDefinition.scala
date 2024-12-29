// SPDX-License-Identifier: Apache-2.0
package org.llvm.circt.scalalib

import org.llvm.mlir.scalalib.*

import java.lang.foreign.{Arena, MemorySegment}

class FirrtlBundleField(val _segment: MemorySegment)

class FirrtlClassElement(val _segment: MemorySegment)

trait DialectHandleApi:
  extension (context: Context)
    inline def loadFirrtlDialect(
    )(
      using arena: Arena
    ): Unit
    inline def loadChirrtlDialect(
    )(
      using arena: Arena
    ): Unit
    inline def loadSvDialect(
    )(
      using arena: Arena
    ): Unit
    inline def loadSeqDialect(
    )(
      using arena: Arena
    ): Unit
    inline def loadEmitDialect(
    )(
      using arena: Arena
    ): Unit
end DialectHandleApi

trait AttributeApi:
  inline def getParamDeclAttribute(
    name:        String,
    tpe:         Type,
    value:       String | BigInt | Double
  )(
    using arena: Arena,
    context:     Context
  ): Attribute
  extension (string: String)
    inline def importAnnotationsFromJSONRaw(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (portDirections: Seq[FirrtlDirection])
    inline def attrGetPortDirs(
                            using arena: Arena,
                            context: Context
                          ): Attribute
end AttributeApi

trait ModuleApi:
  extension (module: Module)
    inline def exportFIRRTL(
      callBack:    String => Unit
    )(
      using arena: Arena
    ): Unit
end ModuleApi

trait TypeApi:
  extension (width: Int)
    inline def getUInt(
      using arena: Arena,
      context:     Context
    ): Type
    inline def getSInt(
      using arena: Arena,
      context:     Context
    ): Type
    inline def getAnolog(
      using arena: Arena,
      context:     Context
    ): Type
  inline def getClock(
    using arena: Arena,
    context:     Context
  ): Type

  inline def getReset(
    using arena: Arena,
    context:     Context
  ): Type

  inline def getAsyncReset(
    using arena: Arena,
    context:     Context
  ): Type

  extension (firrtlBundleFields: Seq[FirrtlBundleField])
    inline def getBundle(
      using arena: Arena,
      context:     Context
    ): Type

  inline def getAnyRef(
    using arena: Arena,
    context:     Context
  ): Type

  inline def getInteger(
    using arena: Arena,
    context:     Context
  ): Type

  inline def getDouble(
    using arena: Arena,
    context:     Context
  ): Type

  inline def getString(
    using arena: Arena,
    context:     Context
  ): Type

  inline def getBoolean(
    using arena: Arena,
    context:     Context
  ): Type

  inline def getPath(
    using arena: Arena,
    context:     Context
  ): Type

  inline def getList(
    element:     Type
  )(
    using arena: Arena,
    context:     Context
  ): Type

  inline def getClassTpe(
    name:                String,
    firrtlClassElements: Seq[FirrtlClassElement]
  )(
    using arena:         Arena,
    context:             Context
  ): Type

  inline def getMaskType(
    using arena: Arena,
    context:     Context
  ): Type

  extension (tpe: Type)
    inline def getVector(
      count:       Int
    )(
      using arena: Arena,
      context:     Context
    ):                  Type
    inline def isConst: Boolean
    inline def getConstType(
      using arena: Arena
    ):                  Type
    inline def width(ignoreFlip: Boolean): Long
    inline def isUInt:             Boolean
    inline def isSInt:             Boolean
    inline def isClock:            Boolean
    inline def isReset:            Boolean
    inline def isAsyncReset:       Boolean
    inline def isAnalog:           Boolean
    inline def isVector:           Boolean
    inline def getElementType(
      using arena: Arena
    ):                             Type
    inline def getElementNum:      Long
    inline def isBundle:           Boolean
    inline def isOpenBundle:       Boolean
    inline def getBundleNumFields: Long
    inline def getBundleFieldByIndex(idx: Int)(arena: Arena): FirrtlBundleField
    inline def getBundleFieldIndex(
      fieldName:   String
    )(
      using arena: Arena
    ): Int
    inline def isRef:     Boolean
    inline def toRef(
      forceable:   Boolean
    )(
      using arena: Arena
    ):                    Type
    inline def isAnyRef:  Boolean
    inline def isInteger: Boolean
    inline def isDouble:  Boolean
    inline def isString:  Boolean
    inline def isBoolean: Boolean
    inline def isPath:    Boolean
    inline def isList:    Boolean
    inline def isClass:   Boolean
end TypeApi

trait FirrtlBundleFieldApi extends HasSegment[FirrtlBundleField] with HasSizeOf[FirrtlBundleField]:
  inline def createFirrtlBundleField(
    name:        String,
    isFlip:      Boolean,
    tpe:         Type
  )(
    using arena: Arena,
    context:     Context
  ): FirrtlBundleField
  extension (firrtlBundleField: FirrtlBundleField)
    inline def getName()(using arena: Arena): String
    inline def getIsFlip(): Boolean
    inline def getType(): Type
end FirrtlBundleFieldApi

trait FirrtlClassElementApi extends HasSegment[FirrtlClassElement] with HasSizeOf[FirrtlClassElement]:
  inline def createFirrtlClassElement(
    name:        String,
    direction:   FirrtlDirection,
    tpe:         Type
  )(
    using arena: Arena,
    context:     Context
  ): FirrtlClassElement
end FirrtlClassElementApi

enum FirrtlConvention:
  case Internal
  case Scalarized
end FirrtlConvention

trait FirrtlConventionApi extends HasSizeOf[FirrtlConvention] with EnumHasToNative[FirrtlConvention]

enum FirrtlNameKind:
  case Droppable
  case Interesting
end FirrtlNameKind
trait FirrtlNameKindApi extends HasSizeOf[FirrtlNameKind] with EnumHasToNative[FirrtlNameKind]

enum FirrtlDirection:
  case In
  case Out
end FirrtlDirection
trait FirrtlDirectionApi extends HasSizeOf[FirrtlDirection] with EnumHasToNative[FirrtlDirection]

enum FirrtlRUW:
  case Undefined
  case Old
  case New
end FirrtlRUW

trait FirrtlRUWApi extends HasSizeOf[FirrtlRUW] with EnumHasToNative[FirrtlRUW]

enum FirrtlMemDir:
  case Infer
  case Read
  case Write
  case ReadWrite
end FirrtlMemDir

trait FirrtlMemDirApi extends HasSizeOf[FirrtlMemDir] with EnumHasToNative[FirrtlMemDir]

enum CirctFirtoolPreserveAggregateMode:
  case None
  case OneDimVec
  case Vec
  case All
end CirctFirtoolPreserveAggregateMode

trait CirctFirtoolPreserveAggregateModeApi
    extends HasSizeOf[CirctFirtoolPreserveAggregateMode]
    with EnumHasToNative[CirctFirtoolPreserveAggregateMode]

enum CirctFirtoolPreserveValuesMode:
  case Strip
  case None
  case Named
  case All
end CirctFirtoolPreserveValuesMode

trait CirctFirtoolPreserveValuesModeApi
    extends HasSizeOf[CirctFirtoolPreserveValuesMode]
    with EnumHasToNative[CirctFirtoolPreserveValuesMode]

enum CirctFirtoolBuildMode:
  case Default
  case Debug
  case Release
end CirctFirtoolBuildMode

trait CirctFirtoolBuildModeApi extends HasSizeOf[CirctFirtoolBuildMode] with EnumHasToNative[CirctFirtoolBuildMode]

enum CirctFirtoolRandomKind:
  case None
  case Mem
  case Reg
  case All
end CirctFirtoolRandomKind

trait CirctFirtoolRandomKindApi extends HasSizeOf[CirctFirtoolRandomKind] with EnumHasToNative[CirctFirtoolRandomKind]

enum CirctFirtoolCompanionMode:
  case Bind
  case Instantiate
  case Drop
end CirctFirtoolCompanionMode

trait CirctFirtoolCompanionModeApi
    extends HasSizeOf[CirctFirtoolCompanionMode]
    with EnumHasToNative[CirctFirtoolCompanionMode]

enum CirctFirtoolVerificationFlavor:
  case None
  case IfElseFatal
  case Immediate
  case Sva
end CirctFirtoolVerificationFlavor

trait CirctFirtoolVerificationFlavorApi
    extends HasSizeOf[CirctFirtoolVerificationFlavor]
    with EnumHasToNative[CirctFirtoolVerificationFlavor]
