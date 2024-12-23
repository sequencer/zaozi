// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.internal.NameKind.Droppable
import me.jiuyang.zaozi.internal.{Context, firrtl}
import sourcecode.{File, Line, Name}

trait VecLike[E <: Data]:
  def element: E
  def count:   Int
  def firrtlType = new firrtl.Vector(element.firrtlType, count, false)

object Vec:
  def apply[E <: Data](n: Int, element: E): Vec[E] = new Vec(element, n)
class Vec[E <: Data](val element: E, val count: Int) extends Data with VecLike[E]

given [E <: Data, R <: Referable[Vec[E]]]: RefElement[Vec[E], E, R, Int] with
  extension (ref: R)
    override def ref(
      idx:       Int
    )(
      using ctx: Context,
      file:      File,
      line:      Line,
      valName:   Name
    ): Ref[E] =
      val subaccess = ctx.handler
        .OpBuilder("firrtl.subindex", ctx.currentBlock, ctx.handler.unkLoc)
        .withNamedAttr("index", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), idx))
        .withOperand(ref.refer)
        .withResultInference(1)
        .build()
        .results
        .head
      new Ref[E](subaccess, ref.tpe.element)

given [E <: Data, R <: Referable[Vec[E]], IDX <: Int | Referable[UInt]]: ExtractElement[Vec[E], E, R, IDX] with
  extension (ref: R)
    def extractElement(
      idx:       IDX
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[E] =
      idx match
        case idx: Int       =>
          val subindex = ctx.handler
            .OpBuilder("firrtl.subindex", ctx.currentBlock, ctx.handler.unkLoc)
            .withNamedAttr("index", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), idx))
            .withOperand(ref.refer)
            .withResultInference(1)
            .build()
            .results
            .head
          new Node[E]("", Droppable, ref.tpe.element, subindex)
        case idx: Ref[UInt] =>
          val subaccess = ctx.handler
            .OpBuilder("firrtl.subaccess", ctx.currentBlock, ctx.handler.unkLoc)
            .withOperand(ref.refer)
            .withOperand(idx.refer)
            .withResultInference(1)
            .build()
            .results
            .head
          new Node[E]("", Droppable, ref.tpe.element, subaccess)
