// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.internal.{Context, firrtl}

object AsyncReset:
  def apply(): AsyncReset = new AsyncReset
class AsyncReset extends Data:
  def firrtlType = new firrtl.AsyncReset(false)
