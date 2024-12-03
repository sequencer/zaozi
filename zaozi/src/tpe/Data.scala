// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.internal.{firrtl, Context}

trait Data:
  // only accessed by Builder.
  def firrtlType: firrtl.FirrtlType

trait SourceInfo

given [D <: Data, SRC <: Referable[D], SINK <: Referable[D]]: MonoConnect[D, SRC, SINK] with
  extension (ref: SINK)
    def :=(
      that:      SRC
    )(
      using ctx: Context
    ): Unit =
      ctx.handler
        .OpBuilder("firrtl.connect", ctx.currentBlock, ctx.handler.unkLoc)
        .withOperand( /* dest */ ref.refer)
        .withOperand( /* src */ that.refer)
        .build()
