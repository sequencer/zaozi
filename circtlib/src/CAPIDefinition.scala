// SPDX-License-Identifier: Apache-2.0
package org.llvm.circt.scalalib

import org.llvm.mlir.scalalib.*

import java.lang.foreign.{Arena, MemorySegment}

class FirrtlBundleField(val _segment: MemorySegment)

class FirrtlClassElement(val _segment: MemorySegment)

trait DialectHandleApi:
  extension (context: Context)
    def loadFirrtlDialect(
    )(
      using arena: Arena
    ): Unit
    def loadChirrtlDialect(
    )(
      using arena: Arena
    ): Unit
    def loadSvDialect(
    )(
      using arena: Arena
    ): Unit
    def loadSeqDialect(
    )(
      using arena: Arena
    ): Unit
    def loadEmitDialect(
    )(
      using arena: Arena
    ): Unit
end DialectHandleApi

trait AttributeApi:
  extension (string: String)
    def importAnnotationsFromJSONRaw(
      using arena: Arena,
      context:     Context
    ): Attribute
end AttributeApi

trait ModuleApi:
  extension (module: Module)
    def exportFIRRTL(
      callBack:    String => Unit
    )(
      using arena: Arena
    ): Unit
end ModuleApi

trait TypeApi:
end TypeApi

trait FirrtlBundleFieldApi extends HasSegment[FirrtlBundleField] with HasSizeOf[FirrtlBundleField]:
  def createFirrtlBundleField(
    name:        String,
    isFlip:      Boolean,
    tpe:         Type
  )(
    using arena: Arena,
    context:     Context
  ): FirrtlBundleField
end FirrtlBundleFieldApi

trait FirrtlClassElementApi extends HasSegment[FirrtlClassElement] with HasSizeOf[FirrtlClassElement]:
  def createFirrtlClassElement(
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
