// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.circtlib.{FIRRTLDirection, MlirLocation, MlirType, MlirValue, Ports}
import me.jiuyang.zaozi.internal.{Context, NameKind, Named}

trait Referable[T <: Data]:
  val tpe: T
  var _refer: MlirValue = null
  def refer(
    using ctx: Context
  ): MlirValue =
    if (_refer == null)
      build
      _refer
    else _refer
  def build(
    using ctx: Context
  ):          Unit

class Ref[T <: Data](
  input:   MlirValue,
  val tpe: T)
    extends Referable[T]:
  def build(
    using ctx: Context
  ): Unit =
    _refer = input

// Node is the result of other PrimOp, so input is assigned here.
class Node[T <: Data](
  val name:     String,
  val nameKind: NameKind,
  input:        MlirValue,
  val tpe:      T)
    extends Referable[T]
    with Named:
  def build(
    using ctx: Context
  ) =
    val value = ctx.handler
      .OpBuilder("firrtl.node", ctx.moduleBlock, ctx.handler.unkLoc)
      .withNamedAttr("name", ctx.handler.mlirStringAttrGet(name))
      .withNamedAttr("nameKind", ctx.handler.firrtlAttrGetNameKind(me.jiuyang.zaozi.internal.toMLIR(nameKind)))
      .withNamedAttr("annotations", ctx.handler.emptyArrayAttr)
      .withOperand(input)
      .withResultInference(1)
      .build()
    _refer = value.results.head

class Instance[T <: Bundle](val name: String, val nameKind: NameKind, val moduleName: String, val tpe: T)
    extends Referable[T]
    with Named:
  def build(
    using ctx: Context
  ) =
    val p: Seq[(String, MlirType, FIRRTLDirection, MlirLocation)] = tpe.firrtlType.fields.get.map(bf =>
      (
        bf.name,
        bf.tpe.toMLIR(ctx.handler),
        if (bf.isFlip) FIRRTLDirection.In else FIRRTLDirection.Out,
        ctx.handler.unkLoc
      )
    )
    val ports = Ports(p.map(_._1), p.map(_._2), p.map(_._3), p.map(_._4))
    val value = ctx.handler
      .OpBuilder("firrtl.instance", ctx.moduleBlock, ctx.handler.unkLoc)
      .withNamedAttr("moduleName", ctx.handler.mlirFlatSymbolRefAttrGet(moduleName))
      .withNamedAttr("name", ctx.handler.mlirStringAttrGet(name))
      .withNamedAttr("nameKind", ctx.handler.firrtlAttrGetNameKind(me.jiuyang.zaozi.internal.toMLIR(nameKind)))
      .withNamedAttr("portDirections", ports.dirAttrs(ctx.handler))
      .withNamedAttr("portNames", ports.nameAttrs(ctx.handler))
      .withNamedAttr("portAnnotations", ports.annotationAttrs(ctx.handler))
      .withNamedAttr("annotations", ctx.handler.emptyArrayAttr)
      .withNamedAttr("layers", ctx.handler.emptyArrayAttr)
      // TODO: infer?
      .withResults(ports.types)
      .build()
    _refer = value.results.head

object Wire:
  def apply[T <: Data](name: String, tpe: T) = new Wire(name, NameKind.Interesting, tpe)
class Wire[T <: Data](
  val name:     String,
  val nameKind: NameKind,
  val tpe:      T)
    extends Referable[T]
    with Named:
  def build(
    using ctx: Context
  ) =
    val value = ctx.handler
      .OpBuilder("firrtl.wire", ctx.currentBlock, ctx.handler.unkLoc)
      .withNamedAttr("name", ctx.handler.mlirStringAttrGet(name))
      .withNamedAttr("nameKind", ctx.handler.firrtlAttrGetNameKind(me.jiuyang.zaozi.internal.toMLIR(nameKind)))
      .withNamedAttr("annotations", ctx.handler.emptyArrayAttr)
      .withResult(tpe.firrtlType.toMLIR(ctx.handler))
      .build()
    _refer = value.results.head

object Reg:
  def apply[T <: Data](name: String, tpe: T, clock: Node[Clock]) = new Reg(name, NameKind.Interesting, tpe, clock)
class Reg[T <: Data](
  val name:     String,
  val nameKind: NameKind,
  val tpe:      T,
  clock:        Referable[Clock])
    extends Referable[T]
    with Named:
  def build(
    using ctx: Context
  ) =
    val value = ctx.handler
      .OpBuilder("firrtl.reg", ctx.currentBlock, ctx.handler.unkLoc)
      .withNamedAttr("name", ctx.handler.mlirStringAttrGet(name))
      .withNamedAttr("nameKind", ctx.handler.firrtlAttrGetNameKind(me.jiuyang.zaozi.internal.toMLIR(nameKind)))
      .withNamedAttr("annotations", ctx.handler.emptyArrayAttr)
      .withOperand( /* clockVal */ clock.refer)
      .withResult( /* result */ tpe.firrtlType.toMLIR(ctx.handler))
      .build()
    _refer = value.results.head

object RegInit:
  def apply[T <: Data](
    name:  String,
    tpe:   T,
    clock: Node[Clock],
    reset: Referable[Reset | AsyncReset],
    init:  Referable[T]
  ) =
    new RegInit(name, NameKind.Interesting, tpe, clock, reset, init)
class RegInit[T <: Data](
  val name:     String,
  val nameKind: NameKind,
  val tpe:      T,
  clock:        Referable[Clock],
  reset:        Referable[Reset | AsyncReset],
  init:         Referable[T])
    extends Referable[T]
    with Named:
  def build(
    using ctx: Context
  ) =
    val value = ctx.handler
      .OpBuilder("firrtl.regreset", ctx.currentBlock, ctx.handler.unkLoc)
      .withNamedAttr("name", ctx.handler.mlirStringAttrGet(name))
      .withNamedAttr("nameKind", ctx.handler.firrtlAttrGetNameKind(me.jiuyang.zaozi.internal.toMLIR(nameKind)))
      .withNamedAttr("annotations", ctx.handler.emptyArrayAttr)
      .withOperand( /* clockVal */ clock.refer)
      .withOperand( /* reset */ reset.refer)
      .withOperand( /* init */ init.refer)
      .withResult( /* result */ tpe.firrtlType.toMLIR(ctx.handler))
      .build()
    _refer = value.results.head
