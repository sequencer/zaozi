// SPDX-License-Identifier: Apache-2.0
package me.jiuyang.zaozi.circtlib

import org.llvm.circt
import org.llvm.circt.CAPI

import java.lang.foreign.MemorySegment
import java.lang.foreign.ValueLayout.JAVA_BYTE

case class Ports(names: Seq[String], types: Seq[MlirType], dirs: Seq[FIRRTLDirection], locs: Seq[MlirLocation]):
  def dirAttrs(handler:        CirctHandler) = handler.firrtlAttrGetPortDirs(dirs)
  def nameAttrs(handler:       CirctHandler) = handler.mlirArrayAttrGet(names.map(n => handler.mlirStringAttrGet(n)))
  def typeAttrs(handler:       CirctHandler) = handler.mlirArrayAttrGet(types.map(t => handler.mlirTypeAttrGet(t)))
  def annotationAttrs(handler: CirctHandler) = handler.mlirArrayAttrGet(names.map(_ => handler.emptyArrayAttr))
  def symAttrs(handler:        CirctHandler) = handler.mlirArrayAttrGet(Seq.empty)
  def locAttrs(handler:        CirctHandler) = handler.mlirArrayAttrGet(locs.map(l => handler.mlirLocationGetAttribute(l)))

trait ForeignType[T]:
  def get: T
  val sizeof: Int

case class MlirAttribute(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirAttribute.sizeof().toInt

object MlirAttribute:
  def apply(ptr: MemorySegment) = new MlirAttribute(ptr)

case class MlirNamedAttribute(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirNamedAttribute.sizeof().toInt

object MlirNamedAttribute:
  def apply(ptr: MemorySegment) = new MlirNamedAttribute(ptr)

case class MlirBlock(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirBlock.sizeof().toInt

object MlirBlock:
  def apply(ptr: MemorySegment) = new MlirBlock(ptr)

case class MlirRegion(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirRegion.sizeof().toInt

object MlirRegion:
  def apply(ptr: MemorySegment) = new MlirRegion(ptr)

case class MlirIdentifier(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirIdentifier.sizeof().toInt

object MlirIdentifier:
  def apply(ptr: MemorySegment) = new MlirIdentifier(ptr)

case class MlirLocation(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirLocation.sizeof().toInt

object MlirLocation:
  def apply(ptr: MemorySegment) = new MlirLocation(ptr)

case class MlirModule(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirModule.sizeof().toInt

object MlirModule:
  def apply(ptr: MemorySegment) = new MlirModule(ptr)

case class MlirOperation(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirOperation.sizeof().toInt

object MlirOperation:
  def apply(ptr: MemorySegment) = new MlirOperation(ptr)

case class MlirOperationState(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirOperationState.sizeof().toInt

object MlirOperationState:
  def apply(ptr: MemorySegment) = new MlirOperationState(ptr)

case class MlirType(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirType.sizeof().toInt

object MlirType:
  def apply(ptr: MemorySegment) = new MlirType(ptr)

case class MlirValue(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirValue.sizeof().toInt

object MlirValue:
  def apply(ptr: MemorySegment) = new MlirValue(ptr)

case class MlirStringRef(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirStringRef.sizeof().toInt

  def toBytes: Array[Byte] =
    val slice = circt.MlirStringRef.data$get(ptr).asSlice(0, circt.MlirStringRef.length$get(ptr))
    slice.toArray(JAVA_BYTE)

  override def toString: String = new String(toBytes)

object MlirStringRef:
  def apply(ptr: MemorySegment) = new MlirStringRef(ptr)

case class MlirLogicalResult(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirLogicalResult.sizeof().toInt

object MlirLogicalResult:
  def apply(ptr: MemorySegment) = new MlirLogicalResult(ptr)

case class MlirStringCallback(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = CAPI.C_POINTER.byteSize().toInt

object MlirStringCallback:
  def apply(ptr: MemorySegment) = new MlirStringCallback(ptr)

case class MlirPassManager(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirPassManager.sizeof().toInt

object MlirPassManager:
  def apply(ptr: MemorySegment) = new MlirPassManager(ptr)

case class MlirOpPassManager(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirOpPassManager.sizeof().toInt

object MlirOpPassManager:
  def apply(ptr: MemorySegment) = new MlirOpPassManager(ptr)

case class MlirPass(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.MlirPass.sizeof().toInt

object MlirPass:
  def apply(ptr: MemorySegment) = new MlirPass(ptr)

case class FIRRTLBundleField(name: String, isFlip: Boolean, tpe: MlirType)

case class FIRRTLClassElement(name: String, tpe: MlirType, direction: FIRRTLDirection)

case class CirctFirtoolFirtoolOptions(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.CirctFirtoolFirtoolOptions.sizeof().toInt

object CirctFirtoolFirtoolOptions:
  def apply(ptr: MemorySegment) = new CirctFirtoolFirtoolOptions(ptr)

case class OMEvaluator(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.OMEvaluator.sizeof().toInt

object OMEvaluator:
  def apply(ptr: MemorySegment) = new OMEvaluator(ptr)

case class OMEvaluatorValue(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.OMEvaluatorValue.sizeof().toInt

object OMEvaluatorValue:
  def apply(ptr: MemorySegment) = new OMEvaluatorValue(ptr)

case class HWInstanceGraph(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.HWInstanceGraph.sizeof().toInt

object HWInstanceGraph:
  def apply(ptr: MemorySegment) = new HWInstanceGraph(ptr)

case class HWInstanceGraphNode(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = circt.HWInstanceGraphNode.sizeof().toInt

object HWInstanceGraphNode:
  def apply(ptr: MemorySegment) = new HWInstanceGraphNode(ptr)

case class HWInstanceGraphNodeCallback(ptr: MemorySegment) extends ForeignType[MemorySegment]:
  def get:    MemorySegment = ptr
  val sizeof: Int           = CAPI.C_POINTER.byteSize().toInt

object HWInstanceGraphNodeCallback:
  def apply(ptr: MemorySegment) = new HWInstanceGraphNodeCallback(ptr)

//
// MLIR & CIRCT Enums
//

sealed abstract class FIRRTLConvention(val value: Int) extends ForeignType[Int]:
  def get: Int = value
  val sizeof = 4 // FIXME: jextract doesn't export type for C enum

object FIRRTLConvention:
  case object Internal   extends FIRRTLConvention(value = CAPI.FIRRTL_CONVENTION_INTERNAL())
  case object Scalarized extends FIRRTLConvention(value = CAPI.FIRRTL_CONVENTION_SCALARIZED())

sealed abstract class FIRRTLNameKind(val value: Int) extends ForeignType[Int]:
  def get: Int = value
  val sizeof = 4 // FIXME: jextract doesn't export type for C enum

object FIRRTLNameKind:
  case object DroppableName   extends FIRRTLNameKind(value = CAPI.FIRRTL_NAME_KIND_DROPPABLE_NAME())
  case object InterestingName extends FIRRTLNameKind(value = CAPI.FIRRTL_NAME_KIND_INTERESTING_NAME())

sealed abstract class FIRRTLDirection(val value: Int) extends ForeignType[Int]:
  def get: Int = value
  val sizeof = 4 // FIXME: jextract doesn't export type for C enum

object FIRRTLDirection:
  case object In  extends FIRRTLDirection(value = CAPI.FIRRTL_DIRECTION_IN())
  case object Out extends FIRRTLDirection(value = CAPI.FIRRTL_DIRECTION_OUT())

sealed abstract class FIRRTLRUW(val value: Int) extends ForeignType[Int]:
  def get: Int = value
  val sizeof = 4 // FIXME: jextract doesn't export type for C enum

object FIRRTLRUW:
  case object Undefined extends FIRRTLRUW(value = CAPI.FIRRTL_RUW_UNDEFINED())
  case object Old       extends FIRRTLRUW(value = CAPI.FIRRTL_RUW_OLD())
  case object New       extends FIRRTLRUW(value = CAPI.FIRRTL_RUW_NEW())

sealed abstract class FIRRTLMemDir(val value: Int) extends ForeignType[Int]:
  def get: Int = value
  val sizeof = 4 // FIXME: jextract doesn't export type for C enum

object FIRRTLMemDir:
  case object Infer     extends FIRRTLMemDir(value = CAPI.FIRRTL_MEM_DIR_INFER())
  case object Read      extends FIRRTLMemDir(value = CAPI.FIRRTL_MEM_DIR_READ())
  case object Write     extends FIRRTLMemDir(value = CAPI.FIRRTL_MEM_DIR_WRITE())
  case object ReadWrite extends FIRRTLMemDir(value = CAPI.FIRRTL_MEM_DIR_READ_WRITE())

sealed class CirctFirtoolPreserveAggregateMode(val value: Int) extends ForeignType[Int]:
  def get: Int = value
  val sizeof = 4 // FIXME: jextract doesn't export type for C enum

object CirctFirtoolPreserveAggregateMode:
  case object None extends CirctFirtoolPreserveAggregateMode(value = CAPI.CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_NONE())
  case object OneDimVec
      extends CirctFirtoolPreserveAggregateMode(value = CAPI.CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_ONE_DIM_VEC())
  case object Vec  extends CirctFirtoolPreserveAggregateMode(value = CAPI.CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_VEC())
  case object All  extends CirctFirtoolPreserveAggregateMode(value = CAPI.CIRCT_FIRTOOL_PRESERVE_AGGREGATE_MODE_ALL())

sealed class CirctFirtoolPreserveValuesMode(val value: Int) extends ForeignType[Int]:
  def get: Int = value
  val sizeof = 4 // FIXME: jextract doesn't export type for C enum

object CirctFirtoolPreserveValuesMode:
  case object Strip extends CirctFirtoolPreserveValuesMode(value = CAPI.CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_STRIP())
  case object None  extends CirctFirtoolPreserveValuesMode(value = CAPI.CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_NONE())
  case object Named extends CirctFirtoolPreserveValuesMode(value = CAPI.CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_NAMED())
  case object All   extends CirctFirtoolPreserveValuesMode(value = CAPI.CIRCT_FIRTOOL_PRESERVE_VALUES_MODE_ALL())

sealed class CirctFirtoolBuildMode(val value: Int) extends ForeignType[Int]:
  def get: Int = value
  val sizeof = 4 // FIXME: jextract doesn't export type for C enum

object CirctFirtoolBuildMode:
  case object Default extends CirctFirtoolBuildMode(value = CAPI.CIRCT_FIRTOOL_BUILD_MODE_DEFAULT())
  case object Debug   extends CirctFirtoolBuildMode(value = CAPI.CIRCT_FIRTOOL_BUILD_MODE_DEBUG())
  case object Release extends CirctFirtoolBuildMode(value = CAPI.CIRCT_FIRTOOL_BUILD_MODE_RELEASE())

sealed class CirctFirtoolRandomKind(val value: Int) extends ForeignType[Int]:
  def get: Int = value
  val sizeof = 4 // FIXME: jextract doesn't export type for C enum

object CirctFirtoolRandomKind:
  case object None extends CirctFirtoolRandomKind(value = CAPI.CIRCT_FIRTOOL_RANDOM_KIND_NONE())
  case object Mem  extends CirctFirtoolRandomKind(value = CAPI.CIRCT_FIRTOOL_RANDOM_KIND_MEM())
  case object Reg  extends CirctFirtoolRandomKind(value = CAPI.CIRCT_FIRTOOL_RANDOM_KIND_REG())
  case object All  extends CirctFirtoolRandomKind(value = CAPI.CIRCT_FIRTOOL_RANDOM_KIND_ALL())

sealed class CirctFirtoolCompanionMode(val value: Int) extends ForeignType[Int]:
  def get: Int = value
  val sizeof = 4 // FIXME: jextract doesn't export type for C enum

object CirctFirtoolCompanionMode:
  case object Bind        extends CirctFirtoolCompanionMode(value = CAPI.CIRCT_FIRTOOL_COMPANION_MODE_BIND())
  case object Instantiate extends CirctFirtoolCompanionMode(value = CAPI.CIRCT_FIRTOOL_COMPANION_MODE_INSTANTIATE())
  case object Drop        extends CirctFirtoolCompanionMode(value = CAPI.CIRCT_FIRTOOL_COMPANION_MODE_DROP())

sealed class CirctFirtoolVerificationFlavor(val value: Int) extends ForeignType[Int]:
  def get: Int = value
  val sizeof = 4 // FIXME: jextract doesn't export type for C enum

object CirctFirtoolVerificationFlavor:
  case object None extends CirctFirtoolVerificationFlavor(value = CAPI.CIRCT_FIRTOOL_VERIFICATION_FLAVOR_NONE())
  case object IfElseFatal
      extends CirctFirtoolVerificationFlavor(value = CAPI.CIRCT_FIRTOOL_VERIFICATION_FLAVOR_IF_ELSE_FATAL())
  case object Immediate
      extends CirctFirtoolVerificationFlavor(value = CAPI.CIRCT_FIRTOOL_VERIFICATION_FLAVOR_IMMEDIATE())
  case object Sva  extends CirctFirtoolVerificationFlavor(value = CAPI.CIRCT_FIRTOOL_VERIFICATION_FLAVOR_SVA())
