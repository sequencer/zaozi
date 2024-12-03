// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.internal.{Context, firrtl}

object Clock:
  def apply(): Clock = new Clock
class Clock extends Data:
  def firrtlType = new firrtl.Clock(false)