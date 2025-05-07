// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.firrtl.capi

import org.llvm.circt.*
import org.llvm.circt.CAPI.*
import org.llvm.mlir.scalalib.{
  given_AttributeApi,
  Attribute,
  Context,
  DialectHandle,
  Identifier,
  LogicalResult,
  Module,
  PassManager,
  Type,
  given
}

import java.lang.foreign.{Arena, MemorySegment}

given ModuleApi with
  extension (module: Module)
    inline def exportFIRRTL(
      callback:    String => Unit
    )(
      using arena: Arena
    ): Unit =
      LogicalResult(
        mlirExportFIRRTL(arena, module.segment, callback.stringToStringCallback.segment, MemorySegment.NULL)
      )
    inline def exportVerilog(
      callback:    String => Unit
    )(
      using arena: Arena
    ): LogicalResult =
      LogicalResult(
        mlirExportVerilog(arena, module.segment, callback.stringToStringCallback.segment, MemorySegment.NULL)
      )
    inline def exportSplitVerilog(
      directory:   String
    )(
      using arena: Arena
    ): LogicalResult =
      LogicalResult(mlirExportSplitVerilog(arena, module.segment, directory.toStringRef.segment))
end given

given DialectHandleApi with
  extension (context: Context)
    inline def loadFirrtlDialect(
    )(
      using arena: Arena
    ): Unit =
      DialectHandle(mlirGetDialectHandle__firrtl__(arena)).loadDialect(
        using arena,
        context
      )
end given

given AttributeApi with
  inline def getMemInit(
    filename:    String,
    isBinary:    Boolean,
    isInline:    Boolean
  )(
    using arena: Arena,
    context:     Context
  ): Attribute = Attribute(
    firrtlAttrGetMemInit(
      arena,
      context.segment,
      filename.identifierGet.segment,
      isBinary,
      isInline
    )
  )
  inline def getParamDeclAttribute(
    name:        String,
    tpe:         Type,
    value:       String | BigInt | Double
  )(
    using arena: Arena,
    context:     Context
  ): Attribute =
    Attribute(
      firrtlAttrGetParamDecl(
        arena,
        context.segment,
        name.identifierGet.segment,
        tpe.segment,
        value match
          case string: String => string.stringAttrGet.segment
          case bigInt: BigInt => bigInt.attrGetIntegerFromString(bigInt.bitLength.integerTypeGet).segment
          case double: Double => double.floatAttrDoubleGet(summon[org.llvm.mlir.scalalib.TypeApi].f64TypeGet).segment
      )
    )
  extension (string:                String)
    inline def importAnnotationsFromJSONRaw(
      using arena: Arena,
      context:     Context
    ): Attribute =
      val attribute = summon[org.llvm.mlir.scalalib.AttributeApi].allocateAttribute
      firrtlImportAnnotationsFromJSONRaw(
        context.segment,
        string.toStringRef.segment,
        attribute.segment
      )
      attribute
  extension (bigInt:                BigInt)
    inline def attrGetIntegerFromString(
      tpe:         Type,
      width:       Option[Int] = None
    )(
      using arena: Arena
    ): Attribute =
      Attribute(
        firrtlAttrGetIntegerFromString(
          arena,
          tpe.segment,
          width.getOrElse(tpe.integerTypeGetWidth.toInt),
          bigInt.toString(10).toStringRef.segment,
          10
        )
      )
  extension (firrtlConvention:      FirrtlConvention)
    inline def toAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(firrtlAttrGetConvention(arena, context.segment, firrtlConvention.toNative))
  extension (firrtlLayerConvention: FirrtlLayerConvention)
    inline def toAttribute(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(firrtlAttrGetLayerConvention(arena, context.segment, firrtlLayerConvention.toNative))
  extension (ruw:                   FirrtlRUW)
    inline def toAttribute(
      using arena: Arena,
      context:     Context
    ): MemorySegment = firrtlAttrGetRUW(arena, context.segment, ruw.toNative)
  extension (memDir:                FirrtlMemDir)
    inline def toAttribute(
      using arena: Arena,
      context:     Context
    ): MemorySegment = firrtlAttrGetMemDir(arena, context.segment, memDir.toNative)
  extension (string:                String)
    inline def innerSymAttrGet(
      using arena: Arena,
      context:     Context
    ) = Attribute(hwInnerSymAttrGet(arena, string.stringAttrGet.segment))
  extension (portDirections:        Seq[FirrtlDirection])
    inline def attrGetPortDirs(
      using arena: Arena,
      context:     Context
    ): Attribute =
      Attribute(firrtlAttrGetPortDirs(arena, context.segment, portDirections.size, portDirections.toMlirArray))
end given

given TypeApi with
  extension (width:              Int)
    inline def getUInt(
      using arena: Arena,
      context:     Context
    ): Type = Type(firrtlTypeGetUInt(arena, context.segment, width))
    inline def getSInt(
      using arena: Arena,
      context:     Context
    ): Type = Type(firrtlTypeGetSInt(arena, context.segment, width))
    inline def getAnalog(
      using arena: Arena,
      context:     Context
    ): Type = Type(firrtlTypeGetAnalog(arena, context.segment, width))
  inline def getClock(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetClock(arena, context.segment))
  inline def getReset(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetReset(arena, context.segment))
  inline def getAsyncReset(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetAsyncReset(arena, context.segment))
  extension (firrtlBundleFields: Seq[FirrtlBundleField])
    inline def getBundle(
      using arena: Arena,
      context:     Context
    ): Type =
      val buffer = FIRRTLBundleField.allocateArray(firrtlBundleFields.size, arena)
      firrtlBundleFields.zipWithIndex.foreach:
        case (field, i) =>
          buffer.asSlice(field.sizeOf * i, field.sizeOf).copyFrom(field.segment)
      Type(firrtlTypeGetBundle(arena, context.segment, firrtlBundleFields.size, buffer))
  inline def getAnyRef(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetAnyRef(arena, context.segment))
  inline def getInteger(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetInteger(arena, context.segment))
  inline def getDouble(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetDouble(arena, context.segment))
  inline def getString(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetString(arena, context.segment))
  inline def getBoolean(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetBoolean(arena, context.segment))
  inline def getPath(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetPath(arena, context.segment))
  inline def getList(
    element:     Type
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetList(arena, context.segment, element.segment))
  inline def getClassTpe(
    name:                String,
    firrtlClassElements: Seq[FirrtlClassElement]
  )(
    using arena:         Arena,
    context:             Context
  ): Type =
    val buffer = FIRRTLClassElement.allocateArray(firrtlClassElements.size, arena)
    firrtlClassElements.zipWithIndex.foreach:
      case (element, i) =>
        buffer.asSlice(element.sizeOf * i, element.sizeOf).copyFrom(element.segment)
    Type(firrtlTypeGetClass(arena, context.segment, name.toStringRef.segment, firrtlClassElements.size, buffer))
  inline def getMaskType(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetMaskType(arena, context.segment))
  extension (tpe:                Type)
    inline def getVector(
      count:       Int
    )(
      using arena: Arena,
      context:     Context
    ): Type = Type(firrtlTypeGetVector(arena, context.segment, tpe.segment, count))
    inline def isConst:            Boolean = firrtlTypeIsConst(tpe.segment)
    inline def getConstType(
      using arena: Arena
    ): Type = Type(firrtlTypeGetConstType(arena, tpe.segment, true))
    inline def getBitWidth(ignoreFlip: Boolean): Long = firrtlTypeGetBitWidth(tpe.segment, ignoreFlip)
    inline def isUInt:             Boolean = firrtlTypeIsAUInt(tpe.segment)
    inline def isSInt:             Boolean = firrtlTypeIsASInt(tpe.segment)
    inline def isClock:            Boolean = firrtlTypeIsAClock(tpe.segment)
    inline def isReset:            Boolean = firrtlTypeIsAReset(tpe.segment)
    inline def isAsyncReset:       Boolean = firrtlTypeIsAAsyncReset(tpe.segment)
    inline def isAnalog:           Boolean = firrtlTypeIsAAnalog(tpe.segment)
    inline def isVector:           Boolean = firrtlTypeIsAVector(tpe.segment)
    inline def getElementType(
      using arena: Arena
    ): Type = Type(firrtlTypeGetVectorElement(arena, tpe.segment))
    inline def getElementNum:      Long    = firrtlTypeGetVectorNumElements(tpe.segment)
    inline def isBundle:           Boolean = firrtlTypeIsABundle(tpe.segment)
    inline def isOpenBundle:       Boolean = firrtlTypeIsAOpenBundle(tpe.segment)
    inline def getBundleNumFields: Long    = firrtlTypeGetBundleNumFields(tpe.segment)
    inline def getBundleFieldByIndex(
      idx:         Int
    )(
      using arena: Arena
    ): FirrtlBundleField =
      val buffer = FIRRTLBundleField.allocate(arena)
      firrtlTypeGetBundleFieldByIndex(tpe.segment, idx, buffer)
      FirrtlBundleField(buffer)
    inline def getBundleFieldIndex(
      fieldName:   String
    )(
      using arena: Arena
    ): Int =
      firrtlTypeGetBundleFieldIndex(tpe.segment, fieldName.toStringRef.segment)
    inline def isRef:              Boolean = firrtlTypeIsARef(tpe.segment)
    inline def getRef(
      forceable:   Boolean,
      layer:       Seq[String]
    )(
      using arena: Arena,
      context:     Context
    ): Type =
      // wait for [[https://github.com/llvm/circt/pull/8093]]
      // Type(firrtlTypeGetRef(arena, tpe.segment, forceable, layer.reverse.last.symbolRefAttrGet(layer.drop(1).map(_.flatSymbolRefAttrGet)).segment))
      Type(firrtlTypeGetRef(arena, tpe.segment, forceable))
    inline def isAnyRef:           Boolean = firrtlTypeIsAAnyRef(tpe.segment)
    inline def isInteger:          Boolean = firrtlTypeIsAInteger(tpe.segment)
    inline def isDouble:           Boolean = firrtlTypeIsADouble(tpe.segment)
    inline def isString:           Boolean = firrtlTypeIsAString(tpe.segment)
    inline def isBoolean:          Boolean = firrtlTypeIsABoolean(tpe.segment)
    inline def isPath:             Boolean = firrtlTypeIsAPath(tpe.segment)
    inline def isList:             Boolean = firrtlTypeIsAList(tpe.segment)
    inline def isClass:            Boolean = firrtlTypeIsAClass(tpe.segment)
end given

given FirrtlBundleFieldApi with
  inline def createFirrtlBundleField(
    name:        String,
    isFlip:      Boolean,
    tpe:         Type
  )(
    using arena: Arena,
    context:     Context
  ): FirrtlBundleField =
    val buffer = FIRRTLBundleField.allocate(arena)
    FIRRTLBundleField.name$slice(buffer).copyFrom(name.identifierGet.segment)
    FIRRTLBundleField.isFlip$set(buffer, isFlip)
    FIRRTLBundleField.type$slice(buffer).copyFrom(tpe.segment)
    FirrtlBundleField(buffer)
  extension (firrtlBundleField: FirrtlBundleField)
    inline def getName(
      using arena: Arena
    ): String = Identifier(FIRRTLBundleField.name$slice(firrtlBundleField.segment)).str
    inline def getIsFlip: Boolean = FIRRTLBundleField.isFlip$get(firrtlBundleField.segment)
    inline def getType:   Type    = Type(FIRRTLBundleField.type$slice(firrtlBundleField.segment))

    inline def segment: MemorySegment = firrtlBundleField._segment
    inline def sizeOf:  Int           = FIRRTLBundleField.sizeof().toInt
end given

given FirrtlClassElementApi with
  inline def createFirrtlClassElement(
    name:        String,
    direction:   FirrtlDirection,
    tpe:         Type
  )(
    using arena: Arena,
    context:     Context
  ): FirrtlClassElement =
    val buffer = FIRRTLClassElement.allocate(arena)
    FIRRTLClassElement.name$slice(buffer).copyFrom(name.identifierGet.segment)
    FIRRTLClassElement.direction$set(buffer, direction.toNative)
    FIRRTLClassElement.type$slice(buffer).copyFrom(tpe.segment)
    FirrtlClassElement(buffer)
  extension (firrtlClassElement: FirrtlClassElement)
    inline def segment: MemorySegment = firrtlClassElement._segment
    inline def sizeOf:  Int           = FIRRTLClassElement.sizeof().toInt
end given

given FirrtlEventControlApi with
  extension (int: Int)
    override inline def fromNative: FirrtlEventControl = int match
      case i if i == FIRRTL_EVENT_CONTROL_AT_POS_EDGE() => FirrtlEventControl.AtPostEdge
      case i if i == FIRRTL_EVENT_CONTROL_AT_NEG_EDGE() => FirrtlEventControl.AtNegEdge
      case i if i == FIRRTL_EVENT_CONTROL_AT_EDGE()     => FirrtlEventControl.AtEdge
  extension (ref: FirrtlEventControl)
    inline def toNative: Int =
      ref match
        case FirrtlEventControl.AtPostEdge => FIRRTL_EVENT_CONTROL_AT_POS_EDGE()
        case FirrtlEventControl.AtNegEdge  => FIRRTL_EVENT_CONTROL_AT_NEG_EDGE()
        case FirrtlEventControl.AtEdge     => FIRRTL_EVENT_CONTROL_AT_EDGE()
    inline def sizeOf:   Int = 4
  extension (ref: FirrtlEventControl)
    inline def attrGetEventControl(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(
      firrtlAttrGetEventControl(arena, context.segment, ref.toNative)
    )

given FirrtlConventionApi with
  extension (int: Int)
    override inline def fromNative: FirrtlConvention = int match
      case i if i == FIRRTL_CONVENTION_INTERNAL()   => FirrtlConvention.Internal
      case i if i == FIRRTL_CONVENTION_SCALARIZED() => FirrtlConvention.Scalarized
  extension (ref: FirrtlConvention)
    inline def toNative: Int =
      ref match
        case FirrtlConvention.Internal   => FIRRTL_CONVENTION_INTERNAL()
        case FirrtlConvention.Scalarized => FIRRTL_CONVENTION_SCALARIZED()
    inline def sizeOf:   Int = 4
end given

given FirrtlLayerConventionApi with
  extension (int: Int)
    override inline def fromNative: FirrtlLayerConvention = int match
      case i if i == FIRRTL_LAYER_CONVENTION_BIND()   => FirrtlLayerConvention.Bind
      case i if i == FIRRTL_LAYER_CONVENTION_INLINE() => FirrtlLayerConvention.Inline
  extension (ref: FirrtlLayerConvention)
    inline def toNative: Int =
      ref match
        case FirrtlLayerConvention.Bind   => FIRRTL_LAYER_CONVENTION_BIND()
        case FirrtlLayerConvention.Inline => FIRRTL_LAYER_CONVENTION_INLINE()
    inline def sizeOf:   Int = 4
end given

given FirrtlNameKindApi with
  extension (int: Int)
    override inline def fromNative: FirrtlNameKind = int match
      case i if i == FIRRTL_NAME_KIND_DROPPABLE_NAME()   => FirrtlNameKind.Droppable
      case i if i == FIRRTL_NAME_KIND_INTERESTING_NAME() => FirrtlNameKind.Interesting
  extension (ref: FirrtlNameKind)
    inline def attrGetNameKind(
      using arena: Arena,
      context:     Context
    ): Attribute = Attribute(firrtlAttrGetNameKind(arena, context.segment, ref.toNative))
    inline def toNative: Int =
      ref match
        case FirrtlNameKind.Droppable   => FIRRTL_NAME_KIND_DROPPABLE_NAME()
        case FirrtlNameKind.Interesting => FIRRTL_NAME_KIND_INTERESTING_NAME()
    inline def sizeOf:   Int = 4
end given

given FirrtlDirectionApi with
  extension (int: Int)
    override inline def fromNative: FirrtlDirection = int match
      case i if i == FIRRTL_DIRECTION_IN()  => FirrtlDirection.In
      case i if i == FIRRTL_DIRECTION_OUT() => FirrtlDirection.Out
  extension (ref: FirrtlDirection)
    inline def toNative: Int =
      ref match
        case FirrtlDirection.In  => FIRRTL_DIRECTION_IN()
        case FirrtlDirection.Out => FIRRTL_DIRECTION_OUT()
    inline def sizeOf:   Int = 4
end given

given FirrtlRUWApi with
  extension (int: Int)
    override inline def fromNative: FirrtlRUW = int match
      case i if i == FIRRTL_RUW_UNDEFINED() => FirrtlRUW.Undefined
      case i if i == FIRRTL_RUW_OLD()       => FirrtlRUW.Old
      case i if i == FIRRTL_RUW_NEW()       => FirrtlRUW.New
  extension (ref: FirrtlRUW)
    inline def toNative: Int = ref match
      case FirrtlRUW.Undefined => FIRRTL_RUW_UNDEFINED()
      case FirrtlRUW.Old       => FIRRTL_RUW_OLD()
      case FirrtlRUW.New       => FIRRTL_RUW_NEW()
    inline def sizeOf:   Int = 4
end given

given FirrtlMemDirApi with
  extension (int: Int)
    override inline def fromNative: FirrtlMemDir = int match
      case i if i == FIRRTL_MEM_DIR_INFER()      => FirrtlMemDir.Infer
      case i if i == FIRRTL_MEM_DIR_READ()       => FirrtlMemDir.Read
      case i if i == FIRRTL_MEM_DIR_WRITE()      => FirrtlMemDir.Write
      case i if i == FIRRTL_MEM_DIR_READ_WRITE() => FirrtlMemDir.ReadWrite
  extension (ref: FirrtlMemDir)
    inline def toNative: Int = ref match
      case FirrtlMemDir.Infer     => FIRRTL_MEM_DIR_INFER()
      case FirrtlMemDir.Read      => FIRRTL_MEM_DIR_READ()
      case FirrtlMemDir.Write     => FIRRTL_MEM_DIR_WRITE()
      case FirrtlMemDir.ReadWrite => FIRRTL_MEM_DIR_READ_WRITE()
    inline def sizeOf:   Int = 4
end given

given CirctFirtoolPreserveAggregateModeApi with
  extension (int: Int)
    override inline def fromNative: CirctFirtoolPreserveAggregateMode = int match
      case i if i == CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_NONE()        => CirctFirtoolPreserveAggregateMode.None
      case i if i == CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_ONE_DIM_VEC() => CirctFirtoolPreserveAggregateMode.OneDimVec
      case i if i == CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_VEC()         => CirctFirtoolPreserveAggregateMode.Vec
      case i if i == CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_ALL()         => CirctFirtoolPreserveAggregateMode.All
  extension (ref: CirctFirtoolPreserveAggregateMode)
    inline def toNative: Int = ref match
      case CirctFirtoolPreserveAggregateMode.None      => CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_NONE()
      case CirctFirtoolPreserveAggregateMode.OneDimVec => CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_ONE_DIM_VEC()
      case CirctFirtoolPreserveAggregateMode.Vec       => CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_VEC()
      case CirctFirtoolPreserveAggregateMode.All       => CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_ALL()
    inline def sizeOf:   Int = 4
end given

given CirctFirtoolPreserveValuesModeApi with
  extension (int: Int)
    override inline def fromNative: CirctFirtoolPreserveValuesMode = int match
      case i if i == CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_STRIP() => CirctFirtoolPreserveValuesMode.Strip
      case i if i == CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_NONE()  => CirctFirtoolPreserveValuesMode.None
      case i if i == CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_NAMED() => CirctFirtoolPreserveValuesMode.Named
      case i if i == CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_ALL()   => CirctFirtoolPreserveValuesMode.All
  extension (ref: CirctFirtoolPreserveValuesMode)
    inline def toNative: Int = ref match
      case CirctFirtoolPreserveValuesMode.Strip => CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_STRIP()
      case CirctFirtoolPreserveValuesMode.None  => CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_NONE()
      case CirctFirtoolPreserveValuesMode.Named => CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_NAMED()
      case CirctFirtoolPreserveValuesMode.All   => CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_ALL()
    inline def sizeOf:   Int = 4
end given

given CirctFirtoolBuildModeApi with
  extension (int: Int)
    override inline def fromNative: CirctFirtoolBuildMode = int match
      case i if i == CIRCT_FIRTOOL_BUILD_MODE_DEFAULT() => CirctFirtoolBuildMode.Default
      case i if i == CIRCT_FIRTOOL_BUILD_MODE_DEBUG()   => CirctFirtoolBuildMode.Debug
      case i if i == CIRCT_FIRTOOL_BUILD_MODE_RELEASE() => CirctFirtoolBuildMode.Release
  extension (ref: CirctFirtoolBuildMode)
    inline def toNative: Int = ref match
      case CirctFirtoolBuildMode.Default => CIRCT_FIRTOOL_BUILD_MODE_DEFAULT()
      case CirctFirtoolBuildMode.Debug   => CIRCT_FIRTOOL_BUILD_MODE_DEBUG()
      case CirctFirtoolBuildMode.Release => CIRCT_FIRTOOL_BUILD_MODE_RELEASE()
    inline def sizeOf:   Int = 4
end given

given CirctFirtoolRandomKindApi with
  extension (int: Int)
    override inline def fromNative: CirctFirtoolRandomKind = int match
      case i if i == CIRCT_FIRTOOL_RANDOM_KIND_NONE() => CirctFirtoolRandomKind.None
      case i if i == CIRCT_FIRTOOL_RANDOM_KIND_MEM()  => CirctFirtoolRandomKind.Mem
      case i if i == CIRCT_FIRTOOL_RANDOM_KIND_REG()  => CirctFirtoolRandomKind.Reg
      case i if i == CIRCT_FIRTOOL_RANDOM_KIND_ALL()  => CirctFirtoolRandomKind.All
  extension (ref: CirctFirtoolRandomKind)
    inline def toNative: Int = ref match
      case CirctFirtoolRandomKind.None => CIRCT_FIRTOOL_RANDOM_KIND_NONE()
      case CirctFirtoolRandomKind.Mem  => CIRCT_FIRTOOL_RANDOM_KIND_MEM()
      case CirctFirtoolRandomKind.Reg  => CIRCT_FIRTOOL_RANDOM_KIND_REG()
      case CirctFirtoolRandomKind.All  => CIRCT_FIRTOOL_RANDOM_KIND_ALL()
    inline def sizeOf:   Int = 4
end given

given CirctFirtoolCompanionModeApi with
  extension (int: Int)
    override inline def fromNative: CirctFirtoolCompanionMode = int match
      case i if i == CIRCT_FIRTOOL_COMPANION_MODE_BIND()        => CirctFirtoolCompanionMode.Bind
      case i if i == CIRCT_FIRTOOL_COMPANION_MODE_INSTANTIATE() => CirctFirtoolCompanionMode.Instantiate
      case i if i == CIRCT_FIRTOOL_COMPANION_MODE_DROP()        => CirctFirtoolCompanionMode.Drop
  extension (ref: CirctFirtoolCompanionMode)
    inline def toNative: Int = ref match
      case CirctFirtoolCompanionMode.Bind        => CIRCT_FIRTOOL_COMPANION_MODE_BIND()
      case CirctFirtoolCompanionMode.Instantiate => CIRCT_FIRTOOL_COMPANION_MODE_INSTANTIATE()
      case CirctFirtoolCompanionMode.Drop        => CIRCT_FIRTOOL_COMPANION_MODE_DROP()
    inline def sizeOf:   Int = 4
end given

given CirctFirtoolVerificationFlavorApi with
  extension (int: Int)
    override inline def fromNative: CirctFirtoolVerificationFlavor = int match
      case i if i == CIRCT_FIRTOOL_VERIFICATION_FLAVOR_NONE()          => CirctFirtoolVerificationFlavor.None
      case i if i == CIRCT_FIRTOOL_VERIFICATION_FLAVOR_IF_ELSE_FATAL() => CirctFirtoolVerificationFlavor.IfElseFatal
      case i if i == CIRCT_FIRTOOL_VERIFICATION_FLAVOR_IMMEDIATE()     => CirctFirtoolVerificationFlavor.Immediate
      case i if i == CIRCT_FIRTOOL_VERIFICATION_FLAVOR_SVA()           => CirctFirtoolVerificationFlavor.Sva
  extension (ref: CirctFirtoolVerificationFlavor)
    inline def toNative: Int = ref match
      case CirctFirtoolVerificationFlavor.None        => CIRCT_FIRTOOL_VERIFICATION_FLAVOR_NONE()
      case CirctFirtoolVerificationFlavor.IfElseFatal => CIRCT_FIRTOOL_VERIFICATION_FLAVOR_IF_ELSE_FATAL()
      case CirctFirtoolVerificationFlavor.Immediate   => CIRCT_FIRTOOL_VERIFICATION_FLAVOR_IMMEDIATE()
      case CirctFirtoolVerificationFlavor.Sva         => CIRCT_FIRTOOL_VERIFICATION_FLAVOR_SVA()
    inline def sizeOf:   Int = 4
end given

given FirtoolOptionsApi with
  inline def createDefault(
  )(
    using arena: Arena
  ): FirtoolOptions = FirtoolOptions(circtFirtoolOptionsCreateDefault(arena))
  extension (firtoolOptions: FirtoolOptions)
    inline def destroy(
    )(
      using Arena
    ): Unit = circtFirtoolOptionsDestroy(firtoolOptions.segment)
    inline def setOutputFilename(
      filename: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetOutputFilename(firtoolOptions.segment, filename.toStringRef.segment)
    inline def setDisableUnknownAnnotations(
      disable: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetDisableUnknownAnnotations(firtoolOptions.segment, disable)
    inline def setDisableAnnotationsClassless(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetDisableAnnotationsClassless(firtoolOptions.segment, value)
    inline def setLowerAnnotationsNoRefTypePorts(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetLowerAnnotationsNoRefTypePorts(firtoolOptions.segment, value)
    inline def setAllowAddingPortsOnPublic(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetAllowAddingPortsOnPublic(firtoolOptions.segment, value)
    inline def setPreserveAggregate(
      value: CirctFirtoolPreserveAggregateMode
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetPreserveAggregate(firtoolOptions.segment, value.toNative)
    inline def setPreserveValues(
      value: CirctFirtoolPreserveValuesMode
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetPreserveValues(firtoolOptions.segment, value.toNative)
    inline def setEnableDebugInfo(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetEnableDebugInfo(firtoolOptions.segment, value)
    inline def setBuildMode(
      value: CirctFirtoolBuildMode
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetBuildMode(firtoolOptions.segment, value.toNative)
    inline def setDisableLayerSink(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetDisableLayerSink(firtoolOptions.segment, value)
    inline def setDisableOptimization(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetDisableOptimization(firtoolOptions.segment, value)
    inline def setExportChiselInterface(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetExportChiselInterface(firtoolOptions.segment, value)
    inline def setChiselInterfaceOutDirectory(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetChiselInterfaceOutDirectory(firtoolOptions.segment, value.toStringRef.segment)
    inline def setVbToBv(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetVbToBv(firtoolOptions.segment, value)
    inline def setNoDedup(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetNoDedup(firtoolOptions.segment, value)
    inline def setCompanionMode(
      value: CirctFirtoolCompanionMode
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetCompanionMode(firtoolOptions.segment, value.toNative)
    inline def setDisableAggressiveMergeConnections(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetDisableAggressiveMergeConnections(firtoolOptions.segment, value)
    inline def setLowerMemories(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetLowerMemories(firtoolOptions.segment, value)
    inline def setBlackBoxRootPath(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetBlackBoxRootPath(firtoolOptions.segment, value.toStringRef.segment)
    inline def setReplSeqMem(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetReplSeqMem(firtoolOptions.segment, value)
    inline def setReplSeqMemFile(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetReplSeqMemFile(firtoolOptions.segment, value.toStringRef.segment)
    inline def setExtractTestCode(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetExtractTestCode(firtoolOptions.segment, value)
    inline def setIgnoreReadEnableMem(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetIgnoreReadEnableMem(firtoolOptions.segment, value)
    inline def setDisableRandom(
      value: CirctFirtoolRandomKind
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetDisableRandom(firtoolOptions.segment, value.toNative)
    inline def setOutputAnnotationFilename(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetOutputAnnotationFilename(firtoolOptions.segment, value.toStringRef.segment)
    inline def setEnableAnnotationWarning(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetEnableAnnotationWarning(firtoolOptions.segment, value)
    inline def setAddMuxPragmas(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetAddMuxPragmas(firtoolOptions.segment, value)
    inline def setVerificationFlavor(
      value: CirctFirtoolVerificationFlavor
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetVerificationFlavor(firtoolOptions.segment, value.toNative)
    inline def setEmitSeparateAlwaysBlocks(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetEmitSeparateAlwaysBlocks(firtoolOptions.segment, value)
    inline def setEtcDisableInstanceExtraction(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetEtcDisableInstanceExtraction(firtoolOptions.segment, value)
    inline def setEtcDisableRegisterExtraction(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetEtcDisableRegisterExtraction(firtoolOptions.segment, value)
    inline def setEtcDisableModuleInlining(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetEtcDisableModuleInlining(firtoolOptions.segment, value)
    inline def setAddVivadoRAMAddressConflictSynthesisBugWorkaround(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetAddVivadoRAMAddressConflictSynthesisBugWorkaround(firtoolOptions.segment, value)
    inline def setCkgModuleName(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetCkgModuleName(firtoolOptions.segment, value.toStringRef.segment)
    inline def setCkgInputName(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetCkgInputName(firtoolOptions.segment, value.toStringRef.segment)
    inline def setCkgOutputName(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetCkgOutputName(firtoolOptions.segment, value.toStringRef.segment)
    inline def setCkgEnableName(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetCkgEnableName(firtoolOptions.segment, value.toStringRef.segment)
    inline def setCkgTestEnableName(
      value: String
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetCkgTestEnableName(firtoolOptions.segment, value.toStringRef.segment)
    inline def setExportModuleHierarchy(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetExportModuleHierarchy(firtoolOptions.segment, value)
    inline def setStripFirDebugInfo(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetStripFirDebugInfo(firtoolOptions.segment, value)
    inline def setStripDebugInfo(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetStripDebugInfo(firtoolOptions.segment, value)
    inline def setDisableCSEinClasses(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetDisableCSEinClasses(firtoolOptions.segment, value)
    inline def setSelectDefaultInstanceChoice(
      value: Boolean
    )(
      using Arena
    ): Unit = circtFirtoolOptionsSetSelectDefaultInstanceChoice(firtoolOptions.segment, value)

    inline def segment: MemorySegment = firtoolOptions._segment
    inline def sizeOf:  Int           = CirctFirtoolFirtoolOptions.sizeof().toInt
end given

given PassManagerApi with
  extension (pm: PassManager)
    def populatePreprocessTransforms(
      firtoolOptions: FirtoolOptions
    )(
      using Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulatePreprocessTransforms(summon[Arena], pm.segment, firtoolOptions.segment)
    )
    // See inputFilename usage in https://github.com/llvm/circt/blob/ff847edb042541c44c79b59f1a680f641241b485/lib/Firtool/Firtool.cpp#L254
    def populateCHIRRTLToLowFIRRTL(
      firtoolOptions: FirtoolOptions
    )(
      using Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulateCHIRRTLToLowFIRRTL(
        summon[Arena],
        pm.segment,
        firtoolOptions.segment
      )
    )
    def populateLowFIRRTLToHW(
      firtoolOptions: FirtoolOptions,
      inputFilename:  String
    )(
      using Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulateLowFIRRTLToHW(
        summon[Arena],
        pm.segment,
        firtoolOptions.segment,
        inputFilename.toStringRef.segment
      )
    )
    def populateHWToSV(
      firtoolOptions: FirtoolOptions
    )(
      using Arena
    ): LogicalResult = LogicalResult(circtFirtoolPopulateHWToSV(summon[Arena], pm.segment, firtoolOptions.segment))
    def populateExportVerilog(
      firtoolOptions: FirtoolOptions,
      callback:       String => Unit
    )(
      using Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulateExportVerilog(
        summon[Arena],
        pm.segment,
        firtoolOptions.segment,
        callback.stringToStringCallback.segment,
        MemorySegment.NULL
      )
    )
    def populateExportSplitVerilog(
      firtoolOptions: FirtoolOptions,
      directory:      String
    )(
      using Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulateExportSplitVerilog(
        summon[Arena],
        pm.segment,
        firtoolOptions.segment,
        directory.toStringRef.segment
      )
    )
    def populateFinalizeIR(
      firtoolOptions: FirtoolOptions
    )(
      using Arena
    ): LogicalResult = LogicalResult(
      circtFirtoolPopulateFinalizeIR(summon[Arena], pm.segment, firtoolOptions.segment)
    )
end given
