// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.circtlib.MlirValue
import me.jiuyang.zaozi.internal.{firrtl, Context}

trait VecLike[E <: Data] extends SubIdx[E, Int | Ref[UInt]]:
  def element: E
  def count:   Int
  def firrtlType = new firrtl.Vector(element.firrtlType, count, false)

  def getRefViaIdx(
    refer:   MlirValue,
    idx:     Int | Ref[UInt],
    ctx:     Context,
    file:    sourcecode.File,
    line:    sourcecode.Line,
    valName: sourcecode.Name
  ): Ref[E] =
    idx match
      case idx: Int       =>
        val subaccess = ctx.handler
          .OpBuilder("firrtl.subindex", ctx.currentBlock, ctx.handler.unkLoc)
          .withNamedAttr("index", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), idx))
          .withOperand(refer)
          .withResultInference(1)
          .build()
          .results
          .head
        new Ref[E](subaccess, element)
      case idx: Ref[UInt] =>
        val subaccess = ctx.handler
          .OpBuilder("firrtl.subaccess", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperand(refer)
          .withOperand(idx.refer)
          .withResultInference(1)
          .build()
          .results
          .head
        new Ref[E](subaccess, element)

object Vec:
  def apply[E <: Data](n: Int, element: E): Vec[E] = new Vec(element, n)
class Vec[E <: Data](val element: E, val count: Int) extends Data with VecLike[E]
