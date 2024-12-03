// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.internal.{Context, firrtl}

object SInt:
  def apply(width: Width): SInt = new SInt(width)
class SInt(width: Width) extends Data:
  def firrtlType = new firrtl.SInt(width.toInt, false)
