// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Yuhang Zeng <unlsycn@unlsycn.com>
package me.jiuyang.omlib

import scala.collection.mutable.LinkedHashMap

import org.llvm.circt.scalalib.om.capi.{_, given}
import org.llvm.circt.scalalib.hw.capi.given_AttributeApi
import org.llvm.mlir.scalalib.{_, given}

import java.lang.foreign.Arena

sealed trait OMValue:
  def value: Any

  def objOpt = this match
    case OMObj(value) => Some(value)
    case _            => None
  def obj    = objOpt.get

  def strOpt = this match
    case OMString(value) => Some(value)
    case _               => None
  def str    = strOpt.get

  def intOpt = this match
    case OMInt(value) => Some(value)
    case _            => None
  def int    = intOpt.get

  def boolOpt = this match
    case OMBool(value) => Some(value)
    case _             => None
  def bool    = boolOpt.get

  def refOpt = this match
    case OMRef(value) => Some(value)
    case _            => None
  def ref    = refOpt.get

  def pathOpt = this match
    case OMPath(value) => Some(value)
    case _             => None
  def path    = pathOpt.get

  def tupleOpt = this match
    case OMTuple(value) => Some(value)
    case _              => None
  def tuple    = tupleOpt.get

  def listOpt = this match
    case OMList(value) => Some(value)
    case _             => None
  def list    = listOpt.get

  def mapOpt = this match
    case OMMap(value) => Some(value)
    case _            => None
  def map    = mapOpt.get

  def flatten: Seq[OMValue] = Seq(this) ++ (this match
    case OMObj(value)   => value.flatMap((_, child) => child.flatten).toSeq
    case OMMap(value)   => value.flatMap((_, child) => child.flatten).toSeq
    case OMList(value)  => value.flatMap(_.flatten).toSeq
    case OMTuple(value) => value._1.flatten ++ value._2.flatten
    case _              => Seq()
  )

end OMValue

case class OMObj(value: LinkedHashMap[String, OMValue]) extends OMValue
case class OMString(value: String)                      extends OMValue
case class OMInt(value: Long)                           extends OMValue
case class OMBool(value: Boolean)                       extends OMValue
case class OMList(value: Array[OMValue])                extends OMValue
case class OMMap(value: LinkedHashMap[String, OMValue]) extends OMValue
case class OMTuple(value: Tuple2[OMValue, OMValue])     extends OMValue
case class OMRef(value: Tuple2[String, String])         extends OMValue
case class OMPath(value: String)                        extends OMValue

extension (evaluatorValue: EvaluatorValue)
  def toScala(
    using Arena,
    Context
  ): OMValue = evaluatorValue match
    case obj if obj.isAObject                =>
      val fieldNames = obj.objectGetFieldNames
      OMObj(
        LinkedHashMap.from(
          Seq
            .tabulate(fieldNames.arrayAttrGetNumElements)(i => fieldNames.arrayAttrGetElement(i).stringAttrGetValue)
            .zipWithIndex
            .map((fieldName, i) => (fieldName, obj.objectGetField(fieldName.stringAttrGet).toScala))
        )
      )
    case primitive if primitive.isAPrimitive =>
      primitive.getPrimitive match
        case string if string.isString        => OMString(string.stringAttrGetValue)
        case int if int.isInteger             => OMInt(int.integerAttrGetValueInt)
        case omInt if omInt.isAIntegerAttr    => OMInt(omInt.integerAttrGetInt.integerAttrGetValueInt)
        case bool if bool.isBool              => OMBool(bool.boolAttrGetValue)
        case listAttr if listAttr.isAListAttr =>
          OMList(
            Array.tabulate(listAttr.listAttrGetNumElements)(i =>
              listAttr.listAttrGetElement(i).toEvaluatorValue.toScala
            )
          )
        case mapAttr if mapAttr.isAMapAttr    =>
          OMMap(
            LinkedHashMap.from(
              Seq.tabulate(mapAttr.mapAttrGetNumElements)(i =>
                (mapAttr.mapAttrGetElementKey(i).str, mapAttr.mapAttrGetElementValue(i).toEvaluatorValue.toScala)
              )
            )
          )
        case ref if ref.isAReferenceAttr      =>
          val innerRef = ref.referenceAttrGetInnerRef
          OMRef((innerRef.innerRefAttrGetModule.stringAttrGetValue, innerRef.innerRefAttrGetName.stringAttrGetValue))
        // TODO: support SymbolRefAttr
        case _                                => throw new Exception(s"Unsupport MLIR Attribute Type")
    case list if list.isAList                =>
      OMList(
        Array.tabulate(list.listGetNumElements)(i => list.listGetElement(i).toScala)
      )
    case map if map.isAMap                   =>
      val keys = map.mapGetKeys
      OMMap(
        LinkedHashMap.from(
          Seq.tabulate(keys.arrayAttrGetNumElements)(i =>
            val key = keys.arrayAttrGetElement(i)
            (key.stringAttrGetValue, map.mapGetElement(key).toScala)
          )
        )
      )
    case tuple if tuple.isATuple             =>
      OMTuple((tuple.tupleGetElement(0).toScala, tuple.tupleGetElement(1).toScala))
    case path if path.isAPath                => OMPath(path.pathGetAsString.stringAttrGetValue)
    case basepath if basepath.isABasePath    => throw new Exception(s"not support BasePath")
    case _                                   => throw new Exception(s"Unsupport ObjectModel Evaluator Type")
