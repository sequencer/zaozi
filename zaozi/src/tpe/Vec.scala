// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.internal.{Context, firrtl}

object Vec:
  def fill[E <: Data](n: Int)(element: E): Vec[E] = new Vec(element, n)
class Vec[E <: Data](element: E, count: Int) extends Data:
  def firrtlType = new firrtl.Vector(element.firrtlType, count, false)
