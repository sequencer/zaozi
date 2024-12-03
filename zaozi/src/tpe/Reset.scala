// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

// Don't support abstract Reset type, that's cancer
object Reset:
  def apply(): Reset = new Reset
type Reset = Bool