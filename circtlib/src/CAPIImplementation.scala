// SPDX-License-Identifier: Apache-2.0
package org.llvm.circt.scalalib

import org.llvm.circt.*
import org.llvm.circt.CAPI.*
import org.llvm.mlir.scalalib.{Attribute, Context, DialectHandle, Module, Type, given}

import java.lang.foreign.{Arena, MemorySegment}

given ModuleApi with
  extension (module: Module)
    def exportFIRRTL(
      callBack:    String => Unit
    )(
      using arena: Arena
    ): Unit =
      mlirExportFIRRTL(arena, module.segment, callBack.toStringCallBack.segment, MemorySegment.NULL)
end given

given DialectHandleApi with
  extension (context: Context)
    def loadFirrtlDialect(
    )(
      using arena: Arena
    ): Unit = context.loadDialect(DialectHandle(mlirGetDialectHandle__firrtl__(arena)))
    def loadChirrtlDialect(
    )(
      using arena: Arena
    ): Unit = context.loadDialect(DialectHandle(mlirGetDialectHandle__chirrtl__(arena)))
    def loadSvDialect(
    )(
      using arena: Arena
    ): Unit = context.loadDialect(DialectHandle(mlirGetDialectHandle__sv__(arena)))
    def loadSeqDialect(
    )(
      using arena: Arena
    ): Unit = context.loadDialect(DialectHandle(mlirGetDialectHandle__seq__(arena)))
    def loadEmitDialect(
    )(
      using arena: Arena
    ): Unit = context.loadDialect(DialectHandle(mlirGetDialectHandle__emit__(arena)))
end given

given AttributeApi with
  def getParamDecl(
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
        name.toStringRef.segment,
        tpe.segment,
        value match
          case string: String => string.toStringAttribute.segment
          case bigInt: BigInt => bigInt.toIntegerAttribute(bigInt.bitLength.toIntegerType).segment
          case double: Double => double.toDoubleAttribute(summon[org.llvm.mlir.scalalib.TypeApi].f64Type).segment
      )
    )
  extension (string:           String)
    def importAnnotationsFromJSONRaw(
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
  extension (bigInt:           BigInt)
    def toIntegerAttribute(
      tpe:         Type
    )(
      using arena: Arena
    ): Attribute =
      Attribute(
        firrtlAttrGetIntegerFromString(
          arena,
          tpe.segment,
          bigInt.bitLength,
          bigInt.toString(10).toStringRef.segment,
          10
        )
      )
  extension (firrtlConvention: FirrtlConvention)
    def toAttribute(
      using arena: Arena,
      context:     Context
    ): MemorySegment = firrtlAttrGetConvention(arena, context.segment, firrtlConvention.toNative)
  extension (nameKind:         FirrtlNameKind)
    def toAttribute(
      using arena: Arena,
      context:     Context
    ): MemorySegment = firrtlAttrGetNameKind(arena, context.segment, nameKind.toNative)
  extension (ruw:              FirrtlRUW)
    def toAttribute(
      using arena: Arena,
      context:     Context
    ): MemorySegment = firrtlAttrGetRUW(arena, context.segment, ruw.toNative)
  extension (memDir:           FirrtlMemDir)
    def toAttribute(
      using arena: Arena,
      context:     Context
    ): MemorySegment = firrtlAttrGetMemDir(arena, context.segment, memDir.toNative)
  extension (portDirections: Seq[FirrtlDirection])
    def toAttribute(
      using arena: Arena,
      context:     Context
    ): MemorySegment =
      val (ptr, length) = portDirections.toMlirArray
      firrtlAttrGetPortDirs(arena, context.segment, length, ptr)
end given

given TypeApi with
  def uintType(
    width:       Int
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetUInt(arena, context.segment, width))
  def sintType(
    width:       Int
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetSInt(arena, context.segment, width))
  def clockType(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetClock(arena, context.segment))
  def resetType(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetReset(arena, context.segment))
  def asyncResetType(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetAsyncReset(arena, context.segment))
  def analogType(
    width:       Int
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetAnalog(arena, context.segment, width))
  def vectorType(
    elementType: Type,
    count:       Int
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetVector(arena, context.segment, elementType.segment, count))
  def bundleType(
    firrtlBundleFields: Seq[FirrtlBundleField]
  )(
    using arena:        Arena,
    context:            Context
  ): Type =
    val buffer = FIRRTLBundleField.allocateArray(firrtlBundleFields.size, arena)
    firrtlBundleFields.zipWithIndex.foreach:
      case (field, i) =>
        buffer.asSlice(field.sizeOf * i, field.sizeOf).copyFrom(field.segment)
    Type(firrtlTypeGetBundle(arena, context.segment, firrtlBundleFields.size, buffer))
  def anyRefType(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetAnyRef(arena, context.segment))
  def integerType(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetAnyRef(arena, context.segment))
  def doubleType(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetDouble(arena, context.segment))
  def stringType(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetString(arena, context.segment))
  def booleanType(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetBoolean(arena, context.segment))
  def pathType(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetPath(arena, context.segment))
  def listType(
    element:     Type
  )(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetList(arena, context.segment, element.segment))
  def classType(
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
  def maskType(
    using arena: Arena,
    context:     Context
  ): Type = Type(firrtlTypeGetMaskType(arena, context.segment))
  extension (tpe: Type)
    def isConst:                                       Boolean = firrtlTypeIsConst(tpe.segment)
    def toConst(
      using arena: Arena
    ): Type = Type(firrtlTypeGetConstType(arena, tpe.segment, true))
    def width(ignoreFlip: Boolean): Long = firrtlTypeGetBitWidth(tpe.segment, ignoreFlip)
    def isUInt:                                        Boolean = firrtlTypeIsAUInt(tpe.segment)
    def isSInt:                                        Boolean = firrtlTypeIsASInt(tpe.segment)
    def isClock:                                       Boolean = firrtlTypeIsAClock(tpe.segment)
    def isReset:                                       Boolean = firrtlTypeIsAReset(tpe.segment)
    def isAsyncReset:                                  Boolean = firrtlTypeIsAAsyncReset(tpe.segment)
    def isAnalog:                                      Boolean = firrtlTypeIsAAnalog(tpe.segment)
    def isVector:                                      Boolean = firrtlTypeIsAVector(tpe.segment)
    def getElementType(
      using arena: Arena
    ): Type = Type(firrtlTypeGetVectorElement(arena, tpe.segment))
    def isBundle:                                      Boolean = firrtlTypeIsABundle(tpe.segment)
    def isOpenBundle:                                  Boolean = firrtlTypeIsAOpenBundle(tpe.segment)
    def getBundleNumFields:                            Long    = firrtlTypeGetBundleNumFields(tpe.segment)
    def getBundleFieldByIndex(idx: Int)(arena: Arena): Type    =
      val buffer = FIRRTLBundleField.allocate(arena)
      firrtlTypeGetBundleFieldByIndex(tpe.segment, idx, buffer)
      Type(buffer)
    def getBundleFieldIndex(
      fieldName:   String
    )(
      using arena: Arena
    ): Int =
      firrtlTypeGetBundleFieldIndex(tpe.segment, fieldName.toStringRef.segment)
    def isRef:                                         Boolean = firrtlTypeIsARef(tpe.segment)
    def toRef(
      forceable:   Boolean
    )(
      using arena: Arena
    ): Type = Type(firrtlTypeGetRef(arena, tpe.segment, forceable))
    def isAnyRef:                                      Boolean = firrtlTypeIsAAnyRef(tpe.segment)
    def isInteger:                                     Boolean = firrtlTypeIsAInteger(tpe.segment)
    def isDouble:                                      Boolean = firrtlTypeIsADouble(tpe.segment)
    def isString:                                      Boolean = firrtlTypeIsAString(tpe.segment)
    def isBoolean:                                     Boolean = firrtlTypeIsABoolean(tpe.segment)
    def isPath:                                        Boolean = firrtlTypeIsAPath(tpe.segment)
    def isList:                                        Boolean = firrtlTypeIsAList(tpe.segment)
    def isClass:                                       Boolean = firrtlTypeIsAClass(tpe.segment)
end given

given FirrtlBundleFieldApi with
  def createFirrtlBundleField(
    name:        String,
    isFlip:      Boolean,
    tpe:         Type
  )(
    using arena: Arena,
    context:     Context
  ): FirrtlBundleField =
    val buffer = FIRRTLBundleField.allocate(arena)
    FIRRTLBundleField.name$slice(buffer).copyFrom(name.toIdentifier.segment)
    FIRRTLBundleField.isFlip$set(buffer, isFlip)
    FIRRTLBundleField.type$slice(buffer).copyFrom(tpe.segment)
    FirrtlBundleField(buffer)
  extension (firrtlBundleField: FirrtlBundleField)
    def segment: MemorySegment = firrtlBundleField._segment
    def sizeOf:  Int           = FIRRTLBundleField.sizeof().toInt
end given

given FirrtlClassElementApi with
  def createFirrtlClassElement(
    name:        String,
    direction:   FirrtlDirection,
    tpe:         Type
  )(
    using arena: Arena,
    context:     Context
  ): FirrtlClassElement =
    val buffer = FIRRTLClassElement.allocate(arena)
    FIRRTLClassElement.name$slice(buffer).copyFrom(name.toIdentifier.segment)
    FIRRTLClassElement.direction$set(buffer, direction.toNative)
    FIRRTLClassElement.type$slice(buffer).copyFrom(tpe.segment)
    FirrtlClassElement(buffer)
  extension (firrtlClassElement: FirrtlClassElement)
    def segment: MemorySegment = firrtlClassElement._segment
    def sizeOf:  Int           = FIRRTLClassElement.sizeof().toInt
end given
given FirrtlConventionApi with
  extension (ref: FirrtlConvention)
    def toNative: Int =
      ref match
        case FirrtlConvention.Internal   => FIRRTL_CONVENTION_INTERNAL()
        case FirrtlConvention.Scalarized => FIRRTL_CONVENTION_SCALARIZED()
    def sizeOf:   Int = 4

end given

given FirrtlNameKindApi with
  extension (ref: FirrtlNameKind)
    def toNative: Int =
      ref match
        case FirrtlNameKind.Droppable   => FIRRTL_NAME_KIND_DROPPABLE_NAME()
        case FirrtlNameKind.Interesting => FIRRTL_NAME_KIND_INTERESTING_NAME()
  extension (ref: FirrtlNameKind) def sizeOf: Int = 4
end given

given FirrtlDirectionApi with
  extension (ref: FirrtlDirection)
    def toNative: Int =
      ref match
        case FirrtlDirection.In  => FIRRTL_DIRECTION_IN()
        case FirrtlDirection.Out => FIRRTL_DIRECTION_OUT()
    def sizeOf:   Int = 4
end given

given FirrtlRUWApi with
  extension (ref: FirrtlRUW)
    def toNative: Int = ref match
      case FirrtlRUW.Undefined => FIRRTL_RUW_UNDEFINED()
      case FirrtlRUW.Old       => FIRRTL_RUW_OLD()
      case FirrtlRUW.New       => FIRRTL_RUW_NEW()
    def sizeOf:   Int = 4
end given

given FirrtlMemDirApi with
  extension (ref: FirrtlMemDir)
    def toNative: Int = ref match
      case FirrtlMemDir.Infer     => FIRRTL_MEM_DIR_INFER()
      case FirrtlMemDir.Read      => FIRRTL_MEM_DIR_READ()
      case FirrtlMemDir.Write     => FIRRTL_MEM_DIR_WRITE()
      case FirrtlMemDir.ReadWrite => FIRRTL_MEM_DIR_READ_WRITE()
    def sizeOf:   Int = 4
end given

given CirctFirtoolPreserveAggregateModeApi with
  extension (ref: CirctFirtoolPreserveAggregateMode)
    def toNative: Int = ref match
      case CirctFirtoolPreserveAggregateMode.None      => CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_NONE()
      case CirctFirtoolPreserveAggregateMode.OneDimVec => CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_ONE_DIM_VEC()
      case CirctFirtoolPreserveAggregateMode.Vec       => CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_VEC()
      case CirctFirtoolPreserveAggregateMode.All       => CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_ALL()
    def sizeOf:   Int = 4
end given

given CirctFirtoolPreserveValuesModeApi with
  extension (ref: CirctFirtoolPreserveValuesMode)
    def toNative: Int = ref match
      case CirctFirtoolPreserveValuesMode.Strip => CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_STRIP()
      case CirctFirtoolPreserveValuesMode.None  => CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_NONE()
      case CirctFirtoolPreserveValuesMode.Named => CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_NAMED()
      case CirctFirtoolPreserveValuesMode.All   => CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_ALL()
    def sizeOf:   Int = 4
end given

given CirctFirtoolBuildModeApi with
  extension (ref: CirctFirtoolBuildMode)
    def toNative: Int = ref match
      case CirctFirtoolBuildMode.Default => CIRCT_FIRTOOL_BUILD_MODE_DEFAULT()
      case CirctFirtoolBuildMode.Debug   => CIRCT_FIRTOOL_BUILD_MODE_DEBUG()
      case CirctFirtoolBuildMode.Release => CIRCT_FIRTOOL_BUILD_MODE_RELEASE()
    def sizeOf:   Int = 4
end given

given CirctFirtoolRandomKindApi with
  extension (ref: CirctFirtoolRandomKind)
    def toNative: Int = ref match
      case CirctFirtoolRandomKind.None => CIRCT_FIRTOOL_RANDOM_KIND_NONE()
      case CirctFirtoolRandomKind.Mem  => CIRCT_FIRTOOL_RANDOM_KIND_MEM()
      case CirctFirtoolRandomKind.Reg  => CIRCT_FIRTOOL_RANDOM_KIND_REG()
      case CirctFirtoolRandomKind.All  => CIRCT_FIRTOOL_RANDOM_KIND_ALL()
    def sizeOf:   Int = 4
end given

given CirctFirtoolCompanionModeApi with
  extension (ref: CirctFirtoolCompanionMode)
    def toNative: Int = ref match
      case CirctFirtoolCompanionMode.Bind        => CIRCT_FIRTOOL_COMPANION_MODE_BIND()
      case CirctFirtoolCompanionMode.Instantiate => CIRCT_FIRTOOL_COMPANION_MODE_INSTANTIATE()
      case CirctFirtoolCompanionMode.Drop        => CIRCT_FIRTOOL_COMPANION_MODE_DROP()
    def sizeOf:   Int = 4
end given

given CirctFirtoolVerificationFlavorApi with
  extension (ref: CirctFirtoolVerificationFlavor)
    def toNative: Int = ref match
      case CirctFirtoolVerificationFlavor.None        => CIRCT_FIRTOOL_VERIFICATION_FLAVOR_NONE()
      case CirctFirtoolVerificationFlavor.IfElseFatal => CIRCT_FIRTOOL_VERIFICATION_FLAVOR_IF_ELSE_FATAL()
      case CirctFirtoolVerificationFlavor.Immediate   => CIRCT_FIRTOOL_VERIFICATION_FLAVOR_IMMEDIATE()
      case CirctFirtoolVerificationFlavor.Sva         => CIRCT_FIRTOOL_VERIFICATION_FLAVOR_SVA()
    def sizeOf:   Int = 4
end given
