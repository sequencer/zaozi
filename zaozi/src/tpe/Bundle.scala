// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.internal.{firrtl, Context}

case class BundleField(name: String, isFlip: Boolean, tpe: Data)
abstract class Bundle extends Data:
  def Aligned[T <: Data](
    data:          T
  )(
    using valName: sourcecode.Name
  ): T =
    elements += BundleField(valName.value, false, data)
    data
  def Flipped[T <: Data](
    data:          T
  )(
    using valName: sourcecode.Name
  ): T =
    elements += BundleField(valName.value, true, data)
    data

  val elements:   collection.mutable.ArrayBuffer[BundleField] = collection.mutable.ArrayBuffer[BundleField]()
  def firrtlType: firrtl.Bundle                               =
    new firrtl.Bundle(elements.toSeq.map(bf => firrtl.BundleField(bf.name, bf.isFlip, bf.tpe.firrtlType)), false)
