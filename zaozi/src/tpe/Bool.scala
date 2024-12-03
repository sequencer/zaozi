// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.internal.{Context, firrtl}

object Bool:
  def apply(): Bool = new Bool
class Bool extends Data:
  def firrtlType = new firrtl.UInt(1.W, false)