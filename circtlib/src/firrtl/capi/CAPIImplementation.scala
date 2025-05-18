// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.firrtl.capi

import org.llvm.circt.*
import org.llvm.circt.CAPI.{mlirGetDialectHandle__firrtl__ as mlirGetDialectHandle, *}
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
  Value,
  given
}

import java.lang.foreign.{Arena, MemorySegment}

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

given FirrtlValueFlowApi with
  extension (int: Int)
    override inline def fromNative: FirrtlValueFlow = int match
      case i if i == FIRRTL_VALUE_FLOW_NONE()   => FirrtlValueFlow.None
      case i if i == FIRRTL_VALUE_FLOW_SOURCE() => FirrtlValueFlow.Source
      case i if i == FIRRTL_VALUE_FLOW_SINK()   => FirrtlValueFlow.Sink
      case i if i == FIRRTL_VALUE_FLOW_DUPLEX() => FirrtlValueFlow.Duplex
  extension (ref: FirrtlValueFlow)
    inline def toNative: Int =
      ref match
        case FirrtlValueFlow.None   => FIRRTL_VALUE_FLOW_NONE()
        case FirrtlValueFlow.Source => FIRRTL_VALUE_FLOW_SOURCE()
        case FirrtlValueFlow.Sink   => FIRRTL_VALUE_FLOW_SINK()
        case FirrtlValueFlow.Duplex => FIRRTL_VALUE_FLOW_DUPLEX()
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
