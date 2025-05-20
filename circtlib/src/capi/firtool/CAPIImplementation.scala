// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.firtool

import org.llvm.circt.CAPI.{
  CIRCT_FIRTOOL_BUILD_MODE_DEBUG,
  CIRCT_FIRTOOL_BUILD_MODE_DEFAULT,
  CIRCT_FIRTOOL_BUILD_MODE_RELEASE,
  CIRCT_FIRTOOL_COMPANION_MODE_BIND,
  CIRCT_FIRTOOL_COMPANION_MODE_DROP,
  CIRCT_FIRTOOL_COMPANION_MODE_INSTANTIATE,
  CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_ALL,
  CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_NONE,
  CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_ONE_DIM_VEC,
  CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_VEC,
  CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_ALL,
  CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_NAMED,
  CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_NONE,
  CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_STRIP,
  CIRCT_FIRTOOL_RANDOM_KIND_ALL,
  CIRCT_FIRTOOL_RANDOM_KIND_MEM,
  CIRCT_FIRTOOL_RANDOM_KIND_NONE,
  CIRCT_FIRTOOL_RANDOM_KIND_REG,
  CIRCT_FIRTOOL_VERIFICATION_FLAVOR_IF_ELSE_FATAL,
  CIRCT_FIRTOOL_VERIFICATION_FLAVOR_IMMEDIATE,
  CIRCT_FIRTOOL_VERIFICATION_FLAVOR_NONE,
  CIRCT_FIRTOOL_VERIFICATION_FLAVOR_SVA
}

import java.lang.foreign.MemorySegment

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
  extension (ref: FirtoolOptions)
    inline def segment: MemorySegment = ref._segment
    inline def sizeOf:  Int           = org.llvm.circt.CirctFirtoolFirtoolOptions.sizeof().toInt
end given
