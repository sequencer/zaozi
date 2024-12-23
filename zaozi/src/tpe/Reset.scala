// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.internal.Context

// Don't support abstract Reset type, that's cancer
object Reset:
  def apply(): Reset = new Reset
type Reset = Bool

trait AsReset[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asReset(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[AsyncReset]
