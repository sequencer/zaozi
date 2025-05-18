// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.firrtl.capi

// circt-c/Dialect/Firrtl.h
import org.llvm.mlir.scalalib.*

import java.lang.foreign.{Arena, MemorySegment}

class FirrtlBundleField(val _segment: MemorySegment)
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
    inline def getName(
      using arena: Arena
    ):                    String
    inline def getIsFlip: Boolean
    inline def getType:   Type
end FirrtlBundleFieldApi

class FirrtlClassElement(val _segment: MemorySegment)
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

class FirtoolOptions(val _segment: MemorySegment)
trait FirtoolOptionsApi extends HasSegment[FirtoolOptions] with HasSizeOf[FirtoolOptions]:
  inline def createDefault(
  )(
    using arena: Arena
  ): FirtoolOptions
  extension (firtoolOptions: FirtoolOptions)
    inline def destroy(
    )(
      using Arena
    ): Unit
    inline def setOutputFilename(
      filename: String
    )(
      using Arena
    ): Unit
    inline def setDisableUnknownAnnotations(
      disable: Boolean
    )(
      using Arena
    ): Unit
    inline def setDisableAnnotationsClassless(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setLowerAnnotationsNoRefTypePorts(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setAllowAddingPortsOnPublic(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setPreserveAggregate(
      value: CirctFirtoolPreserveAggregateMode
    )(
      using Arena
    ): Unit
    inline def setPreserveValues(
      value: CirctFirtoolPreserveValuesMode
    )(
      using Arena
    ): Unit
    inline def setEnableDebugInfo(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setBuildMode(
      value: CirctFirtoolBuildMode
    )(
      using Arena
    ): Unit
    inline def setDisableLayerSink(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setDisableOptimization(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setExportChiselInterface(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setChiselInterfaceOutDirectory(
      value: String
    )(
      using Arena
    ): Unit
    inline def setVbToBv(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setNoDedup(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setCompanionMode(
      value: CirctFirtoolCompanionMode
    )(
      using Arena
    ): Unit
    inline def setDisableAggressiveMergeConnections(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setLowerMemories(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setBlackBoxRootPath(
      value: String
    )(
      using Arena
    ): Unit
    inline def setReplSeqMem(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setReplSeqMemFile(
      value: String
    )(
      using Arena
    ): Unit
    inline def setExtractTestCode(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setIgnoreReadEnableMem(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setDisableRandom(
      value: CirctFirtoolRandomKind
    )(
      using Arena
    ): Unit
    inline def setOutputAnnotationFilename(
      value: String
    )(
      using Arena
    ): Unit
    inline def setEnableAnnotationWarning(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setAddMuxPragmas(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setVerificationFlavor(
      value: CirctFirtoolVerificationFlavor
    )(
      using Arena
    ): Unit
    inline def setEmitSeparateAlwaysBlocks(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setEtcDisableInstanceExtraction(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setEtcDisableRegisterExtraction(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setEtcDisableModuleInlining(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setAddVivadoRAMAddressConflictSynthesisBugWorkaround(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setCkgModuleName(
      value: String
    )(
      using Arena
    ): Unit
    inline def setCkgInputName(
      value: String
    )(
      using Arena
    ): Unit
    inline def setCkgOutputName(
      value: String
    )(
      using Arena
    ): Unit
    inline def setCkgEnableName(
      value: String
    )(
      using Arena
    ): Unit
    inline def setCkgTestEnableName(
      value: String
    )(
      using Arena
    ): Unit
    inline def setExportModuleHierarchy(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setStripFirDebugInfo(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setStripDebugInfo(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setDisableCSEinClasses(
      value: Boolean
    )(
      using Arena
    ): Unit
    inline def setSelectDefaultInstanceChoice(
      value: Boolean
    )(
      using Arena
    ): Unit
end FirtoolOptionsApi

enum FirrtlEventControl:
  case AtPostEdge
  case AtNegEdge
  case AtEdge
end FirrtlEventControl
trait FirrtlEventControlApi extends HasSizeOf[FirrtlEventControl] with EnumHasToNative[FirrtlEventControl]

enum FirrtlConvention:
  case Internal
  case Scalarized
end FirrtlConvention
trait FirrtlConventionApi extends HasSizeOf[FirrtlConvention] with EnumHasToNative[FirrtlConvention]

enum FirrtlLayerConvention:
  case Bind
  case Inline
end FirrtlLayerConvention
trait FirrtlLayerConventionApi extends HasSizeOf[FirrtlLayerConvention] with EnumHasToNative[FirrtlLayerConvention]

enum FirrtlNameKind:
  case Droppable
  case Interesting
end FirrtlNameKind
trait FirrtlNameKindApi extends HasSizeOf[FirrtlNameKind] with EnumHasToNative[FirrtlNameKind]

enum FirrtlValueFlow:
  case None
  case Source
  case Sink
  case Duplex
end FirrtlValueFlow
trait FirrtlValueFlowApi extends HasSizeOf[FirrtlValueFlow] with EnumHasToNative[FirrtlValueFlow]

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

/** Firrtl DialectHandle Api
  * {{{
  * mlirGetDialectHandle__firrtl__
  * }}}
  */
trait DialectApi:
  extension (context: Context)
    inline def loadDialect(
    )(
      using arena: Arena
    ): Unit
end DialectApi

/** Firrtl Attribute Api
  * {{{
  * firrtlAttrGetConvention
  * firrtlAttrGetEventControl
  * firrtlAttrGetIntegerFromString
  * firrtlAttrGetLayerConvention
  * firrtlAttrGetMemDir
  * firrtlAttrGetMemInit
  * firrtlAttrGetNameKind
  * firrtlAttrGetParamDecl
  * firrtlAttrGetPortDirs
  * firrtlAttrGetRUW
  * }}}
  */
trait AttributeApi:
  extension (firrtlConvention:      FirrtlConvention)
    inline def toAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (ref:                   FirrtlEventControl)
    inline def attrGetEventControl(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (bigInt:                BigInt)
    inline def attrGetIntegerFromString(
      tpe:         Type,
      width:       Option[Int] = None
    )(
      using arena: Arena
    ): Attribute
  extension (firrtlLayerConvention: FirrtlLayerConvention)
    inline def toAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (memDir:                FirrtlMemDir)
    inline def toAttribute(
      using arena: Arena,
      context:     Context
    ): MemorySegment
  inline def getMemInit(
    filename:    String,
    isBinary:    Boolean,
    isInline:    Boolean
  )(
    using arena: Arena,
    context:     Context
  ): Attribute
  extension (ref:                   FirrtlNameKind)
    inline def attrGetNameKind(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (value:                 String)
    inline def getParamDeclAttribute(
      name:        String,
      tpe:         Type
    )(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (value:                 BigInt)
    inline def getParamDeclAttribute(
      name:        String,
      tpe:         Type
    )(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (value:                 Double)
    inline def getParamDeclAttribute(
      name:        String,
      tpe:         Type
    )(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (portDirections:        Seq[FirrtlDirection])
    inline def attrGetPortDirs(
      using arena: Arena,
      context:     Context
    ): Attribute
  extension (ruw:                   FirrtlRUW)
    inline def toAttribute(
      using arena: Arena,
      context:     Context
    ): MemorySegment
end AttributeApi

/** Firrtl Type Api
  * {{{
  * firrtlTypeGetAnalog
  * firrtlTypeGetAnyRef
  * firrtlTypeGetAsyncReset
  * firrtlTypeGetBitWidth
  * firrtlTypeGetBoolean
  * firrtlTypeGetBundle
  * firrtlTypeGetBundleFieldByIndex
  * firrtlTypeGetBundleFieldIndex
  * firrtlTypeGetBundleNumFields
  * firrtlTypeGetClass
  * firrtlTypeGetClock
  * firrtlTypeGetConstType
  * firrtlTypeGetDouble
  * firrtlTypeGetInteger
  * firrtlTypeGetList
  * firrtlTypeGetMaskType
  * firrtlTypeGetPath
  * firrtlTypeGetRef
  * firrtlTypeGetReset
  * firrtlTypeGetSInt
  * firrtlTypeGetString
  * firrtlTypeGetUInt
  * firrtlTypeGetVector
  * firrtlTypeGetVectorElement
  * firrtlTypeGetVectorNumElements
  * firrtlTypeIsAAnalog
  * firrtlTypeIsAAnyRef
  * firrtlTypeIsAAsyncReset
  * firrtlTypeIsABoolean
  * firrtlTypeIsABundle
  * firrtlTypeIsAClass
  * firrtlTypeIsAClock
  * firrtlTypeIsADouble
  * firrtlTypeIsAInteger
  * firrtlTypeIsAList
  * firrtlTypeIsAOpenBundle
  * firrtlTypeIsAPath
  * firrtlTypeIsARef
  * firrtlTypeIsAReset
  * firrtlTypeIsASInt
  * firrtlTypeIsAString
  * firrtlTypeIsAUInt
  * firrtlTypeIsAVector
  * firrtlTypeIsConst
  * }}}
  */
trait TypeApi:
  extension (width:              Int)
    inline def getAnalog(
      using arena: Arena,
      context:     Context
    ): Type
  inline def getAnyRef(
    using arena: Arena,
    context:     Context
  ): Type
  inline def getAsyncReset(
    using arena: Arena,
    context:     Context
  ): Type
  extension (tpe:                Type) inline def getBitWidth(ignoreFlip: Boolean): Long
  inline def getBoolean(
    using arena: Arena,
    context:     Context
  ): Type
  extension (firrtlBundleFields: Seq[FirrtlBundleField])
    inline def getBundle(
      using arena: Arena,
      context:     Context
    ): Type
  extension (tpe:                Type)
    inline def getBundleFieldByIndex(
      idx:         Int
    )(
      using arena: Arena
    ):                             FirrtlBundleField
    inline def getBundleFieldIndex(
      fieldName:   String
    )(
      using arena: Arena
    ):                             Int
    inline def getBundleNumFields: Long
  inline def getClassTpe(
    name:                String,
    firrtlClassElements: Seq[FirrtlClassElement]
  )(
    using arena:         Arena,
    context:             Context
  ): Type
  inline def getClock(
    using arena: Arena,
    context:     Context
  ): Type
  extension (tpe:                Type)
    inline def getConstType(
      using arena: Arena
    ): Type
  inline def getDouble(
    using arena: Arena,
    context:     Context
  ): Type
  inline def getInteger(
    using arena: Arena,
    context:     Context
  ): Type
  inline def getList(
    element:     Type
  )(
    using arena: Arena,
    context:     Context
  ): Type
  inline def getMaskType(
    using arena: Arena,
    context:     Context
  ): Type
  inline def getPath(
    using arena: Arena,
    context:     Context
  ): Type
  extension (tpe:                Type)
    inline def getRef(
      forceable:   Boolean,
      layer:       Seq[String]
    )(
      using arena: Arena,
      context:     Context
    ): Type
  inline def getReset(
    using arena: Arena,
    context:     Context
  ): Type
  extension (width:              Int)
    inline def getSInt(
      using arena: Arena,
      context:     Context
    ): Type
  inline def getString(
    using arena: Arena,
    context:     Context
  ): Type
  extension (width:              Int)
    inline def getUInt(
      using arena: Arena,
      context:     Context
    ): Type
  extension (tpe:                Type)
    inline def getVector(
      count:       Int
    )(
      using arena: Arena,
      context:     Context
    ):                              Type
    inline def getVectorElementType(
      using arena: Arena
    ):                              Type
    inline def getVectorElementNum: Long
  extension (tpe:                Type)
    inline def isAnalog:     Boolean
    inline def isAnyRef:     Boolean
    inline def isAsyncReset: Boolean
    inline def isBoolean:    Boolean
    inline def isBundle:     Boolean
    inline def isClass:      Boolean
    inline def isClock:      Boolean
    inline def isDouble:     Boolean
    inline def isInteger:    Boolean
    inline def isList:       Boolean
    inline def isOpenBundle: Boolean
    inline def isPath:       Boolean
    inline def isRef:        Boolean
    inline def isReset:      Boolean
    inline def isSInt:       Boolean
    inline def isString:     Boolean
    inline def isUInt:       Boolean
    inline def isVector:     Boolean
    inline def isConst:      Boolean
end TypeApi

/** Firrtl Utility Api
  * {{{
  * firrtlImportAnnotationsFromJSONRaw
  * firrtlValueFoldFlow
  * }}}
  */
trait UtilityApi:
  inline def importAnnotationsFromJSONRaw(
    annotationsStr: String
  )(
    using arena:    Arena,
    context:        Context
  ): Attribute
  inline def valueFoldFlow(value: Value, flow: FirrtlValueFlow): FirrtlValueFlow
end UtilityApi

// TODO: MOVE OUT
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

trait ModuleApi:
  extension (module: Module)
    inline def exportFIRRTL(
      callBack:    String => Unit
    )(
      using arena: Arena
    ): Unit
    inline def exportVerilog(
      callback:    String => Unit
    )(
      using arena: Arena
    ): LogicalResult
    inline def exportSplitVerilog(
      directory:   String
    )(
      using arena: Arena
    ): LogicalResult
end ModuleApi

trait PassManagerApi:
  extension (pm: PassManager)
    def populatePreprocessTransforms(
      firtoolOptions: FirtoolOptions
    )(
      using Arena
    ): LogicalResult
    def populateCHIRRTLToLowFIRRTL(
      firtoolOptions: FirtoolOptions
    )(
      using Arena
    ): LogicalResult
    // See inputFilename usage in https://github.com/llvm/circt/blob/ff847edb042541c44c79b59f1a680f641241b485/lib/Firtool/Firtool.cpp#L254
    def populateLowFIRRTLToHW(
      firtoolOptions: FirtoolOptions,
      inputFilename:  String
    )(
      using Arena
    ): LogicalResult
    def populateHWToSV(
      firtoolOptions: FirtoolOptions
    )(
      using Arena
    ): LogicalResult
    def populateExportVerilog(
      firtoolOptions: FirtoolOptions,
      callback:       String => Unit
    )(
      using Arena
    ): LogicalResult
    def populateExportSplitVerilog(
      firtoolOptions: FirtoolOptions,
      directory:      String
    )(
      using Arena
    ): LogicalResult
    def populateFinalizeIR(
      firtoolOptions: FirtoolOptions
    )(
      using Arena
    ): LogicalResult
end PassManagerApi
