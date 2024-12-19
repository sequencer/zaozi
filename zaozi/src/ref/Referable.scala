// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.circtlib.*
import me.jiuyang.zaozi.internal.NameKind.Interesting
import me.jiuyang.zaozi.internal.{Context, NameKind, Named}

import scala.language.dynamics

/** Referable is used to contain an AST node that exist in the MLIR. */
trait Referable[T <: Data] extends Dynamic:
  val tpe:   T
  val refer: MlirValue

  /** if [[T]] implements [[DynamicSubfield]], it should return the subfield based on the [[fieldValName]], as well as
    * its type.
    */
  def runtimeSelectDynamic[E <: Data](
    fieldValName: String
  )(
    using ctx:    Context,
    file:         sourcecode.File,
    line:         sourcecode.Line,
    valName:      sourcecode.Name
  ): Ref[E] =
    tpe match
      // current only apply to Bundle
      case dynamicSubfield: DynamicSubfield => dynamicSubfield.getRef[E](refer, fieldValName, ctx, file, line, valName)
      case _ => throw new Exception("Unreachable, macro should have guarded it.")

  /** macro to call [[runtimeSelectDynamic]] */
  transparent inline def selectDynamic[R <: Data](name: String): Any = ${ dynamicSubaccess('this, 'name) }

/** Due to Scala not allowing deferred macro call(calling user defined macro from outer macro). Any implementation to
  * [[DynamicSubfield]] should make sure the dynamic access is to a val that has a return type of [[BundleField]]. For
  * now jiuyang cannot come up with better solution to let user define their own macro, however they can still implement
  * their own [[Bundle]].
  */
trait DynamicSubfield:
  def getRef[E <: Data](
    refer:        MlirValue,
    fieldValName: String,
    ctx:          Context,
    file:         sourcecode.File,
    line:         sourcecode.Line,
    valName:      sourcecode.Name
  ): Ref[E]

type Const[T <: Data] = Ref[T]

class Ref[T <: Data](
  val refer: MlirValue,
  val tpe:   T)
    extends Referable[T]

class Node[T <: Data](
  val name:     String,
  val nameKind: NameKind,
  val tpe:      T,
  val refer:    MlirValue)
    extends Referable[T]
    with Named

object Instance:
  def apply[T <: Bundle](
    moduleName: String,
    tpe:        T
  )(
    using ctx:  Context,
    file:       sourcecode.File,
    line:       sourcecode.Line,
    valName:    sourcecode.Name
  ) =
    val p: Seq[(String, MlirType, FIRRTLDirection, MlirLocation)] = tpe.firrtlType.fields.get.map(bf =>
      (
        bf.name,
        bf.tpe.toMLIR(ctx.handler),
        if (bf.isFlip) FIRRTLDirection.In else FIRRTLDirection.Out,
        SourceLocator(file, line).toMLIR
      )
    )
    val ports = Ports(p.map(_._1), p.map(_._2), p.map(_._3), p.map(_._4))

    // create an instance.
    val instance = ctx.handler
      .OpBuilder("firrtl.instance", ctx.moduleBlock, SourceLocator(file, line).toMLIR)
      .withNamedAttr("moduleName", ctx.handler.mlirFlatSymbolRefAttrGet(moduleName))
      .withNamedAttr("name", ctx.handler.mlirStringAttrGet(valName.value))
      .withNamedAttr("nameKind", ctx.handler.firrtlAttrGetNameKind(me.jiuyang.zaozi.internal.toMLIR(Interesting)))
      .withNamedAttr("portDirections", ports.dirAttrs(ctx.handler))
      .withNamedAttr("portNames", ports.nameAttrs(ctx.handler))
      .withNamedAttr("portAnnotations", ports.annotationAttrs(ctx.handler))
      .withNamedAttr("annotations", ctx.handler.emptyArrayAttr)
      .withNamedAttr("layers", ctx.handler.emptyArrayAttr)
      .withResults(ports.types)
      .build()
      .results

    // create a private module for the instance which will be replaced at the linking procedure.
    if (!ctx.elaboratedModule.contains(moduleName))
      val dummyModule = ctx.handler
        .OpBuilder("firrtl.module", ctx.circuitBlock, SourceLocator(file, line).toMLIR)
        .withRegion(Seq((ports.types, ports.locs)))
        .withNamedAttr("sym_name", ctx.handler.mlirStringAttrGet(moduleName))
        .withNamedAttr("sym_visibility", ctx.handler.mlirStringAttrGet("private"))
        .withNamedAttr("convention", ctx.handler.firrtlAttrGetConvention(FIRRTLConvention.Scalarized))
        .withNamedAttr("annotations", ctx.handler.emptyArrayAttr)
        .withNamedAttr("portDirections", ports.dirAttrs(ctx.handler))
        .withNamedAttr("portNames", ports.nameAttrs(ctx.handler))
        .withNamedAttr("portTypes", ports.typeAttrs(ctx.handler))
        .withNamedAttr("portAnnotations", ports.annotationAttrs(ctx.handler))
        .withNamedAttr("portSyms", ports.symAttrs(ctx.handler))
        .withNamedAttr("portLocations", ports.locAttrs(ctx.handler))
        .build()

      Seq
        .tabulate(p.size)(ctx.handler.mlirBlockGetArgument(dummyModule.region(0).block(0), _))
        .map: p =>
          ctx.handler
            .OpBuilder("firrtl.connect", dummyModule.region(0).block(0), SourceLocator(file, line).toMLIR)
            .withOperand( /* dest */ p)
            .withOperand(
              /* src */ ctx.handler
                .OpBuilder("firrtl.invalidvalue", dummyModule.region(0).block(0), SourceLocator(file, line).toMLIR)
                .withResult(ctx.handler.mlirValueGetType(p))
                .build()
                .results
                .head
            )
            .build()

      // for each ports of the dummy module, invalidate it.

      ctx.elaboratedModule += moduleName

    // create a wire wrapping the interface.
    val interfaceWire: Wire[T] = new Wire[T](
      s"io",
      NameKind.Droppable,
      tpe,
      ctx.handler
        .OpBuilder("firrtl.wire", ctx.currentBlock, SourceLocator(file, line).toMLIR)
        .withNamedAttr("name", ctx.handler.mlirStringAttrGet(s"${valName.value}_io"))
        .withNamedAttr(
          "nameKind",
          ctx.handler.firrtlAttrGetNameKind(me.jiuyang.zaozi.internal.toMLIR(NameKind.Droppable))
        )
        .withNamedAttr("annotations", ctx.handler.emptyArrayAttr)
        .withResult(tpe.firrtlType.toMLIR(ctx.handler))
        .build()
        .results
        .head
    )
    interfaceWire.tpe.elements.zipWithIndex.foreach:
      case (ele, idx) =>
        val io   = instance(idx)
        val wire = ctx.handler
          .OpBuilder("firrtl.subfield", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withNamedAttr("fieldIndex", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), idx))
          .withOperand( /* input */ interfaceWire.refer)
          .withResultInference(1)
          .build()
          .results
          .head
        if (ele.isFlip)
          ctx.handler
            .OpBuilder("firrtl.connect", ctx.currentBlock, SourceLocator(file, line).toMLIR)
            .withOperand( /* dest */ io)
            .withOperand( /* src */ wire)
            .build()
        else
          ctx.handler
            .OpBuilder("firrtl.connect", ctx.currentBlock, SourceLocator(file, line).toMLIR)
            .withOperand( /* dest */ wire)
            .withOperand( /* src */ io)
            .build()
    new Instance[T](
      valName.value,
      NameKind.Interesting,
      moduleName,
      tpe,
      interfaceWire.refer
    )

class Instance[T <: Bundle](
  val name:       String,
  val nameKind:   NameKind,
  val moduleName: String,
  val tpe:        T,
  val refer:      MlirValue)
    extends Referable[T]
    with Named

object Wire:
  def apply[T <: Data](
    tpe:       T
  )(
    using ctx: Context,
    file:      sourcecode.File,
    line:      sourcecode.Line,
    valName:   sourcecode.Name
  ) = new Wire(
    valName.value,
    NameKind.Interesting,
    tpe,
    ctx.handler
      .OpBuilder("firrtl.wire", ctx.currentBlock, SourceLocator(file, line).toMLIR)
      .withNamedAttr("name", ctx.handler.mlirStringAttrGet(valName.value))
      .withNamedAttr("nameKind", ctx.handler.firrtlAttrGetNameKind(me.jiuyang.zaozi.internal.toMLIR(Interesting)))
      .withNamedAttr("annotations", ctx.handler.emptyArrayAttr)
      .withResult(tpe.firrtlType.toMLIR(ctx.handler))
      .build()
      .results
      .head
  )
class Wire[T <: Data](
  val name:     String,
  val nameKind: NameKind,
  val tpe:      T,
  val refer:    MlirValue)
    extends Referable[T]
    with Named

object Reg:
  def apply[C <: Referable[Clock], T <: Data](
    tpe:       T,
    clock:     C
  )(
    using ctx: Context,
    file:      sourcecode.File,
    line:      sourcecode.Line,
    valName:   sourcecode.Name
  ) =
    new Reg(
      valName.value,
      NameKind.Interesting,
      tpe,
      clock,
      ctx.handler
        .OpBuilder("firrtl.reg", ctx.currentBlock, SourceLocator(file, line).toMLIR)
        .withNamedAttr("name", ctx.handler.mlirStringAttrGet(valName.value))
        .withNamedAttr("nameKind", ctx.handler.firrtlAttrGetNameKind(me.jiuyang.zaozi.internal.toMLIR(Interesting)))
        .withNamedAttr("annotations", ctx.handler.emptyArrayAttr)
        .withOperand( /* clockVal */ clock.refer)
        .withResult( /* result */ tpe.firrtlType.toMLIR(ctx.handler))
        .build()
        .results
        .head
    )
class Reg[C <: Referable[Clock], T <: Data](
  val name:     String,
  val nameKind: NameKind,
  val tpe:      T,
  clock:        C,
  val refer:    MlirValue)
    extends Referable[T]
    with Named

object RegInit:
  def apply[C <: Referable[Clock], RT <: Reset | AsyncReset, R <: Referable[RT], I <: Const[T], T <: Data](
    tpe:       T,
    clock:     C,
    reset:     R,
    init:      I
  )(
    using ctx: Context,
    file:      sourcecode.File,
    line:      sourcecode.Line,
    valName:   sourcecode.Name
  ) =
    new RegInit(
      valName.value,
      NameKind.Interesting,
      tpe,
      clock,
      reset,
      init,
      ctx.handler
        .OpBuilder("firrtl.regreset", ctx.currentBlock, SourceLocator(file, line).toMLIR)
        .withNamedAttr("name", ctx.handler.mlirStringAttrGet(valName.value))
        .withNamedAttr("nameKind", ctx.handler.firrtlAttrGetNameKind(me.jiuyang.zaozi.internal.toMLIR(Interesting)))
        .withNamedAttr("annotations", ctx.handler.emptyArrayAttr)
        .withOperand( /* clockVal */ clock.refer)
        .withOperand( /* reset */ reset.refer)
        .withOperand( /* init */ init.refer)
        .withResult( /* result */ tpe.firrtlType.toMLIR(ctx.handler))
        .build()
        .results
        .head
    )
class RegInit[C <: Referable[Clock], RT <: Reset | AsyncReset, R <: Referable[RT], I <: Const[T], T <: Data](
  val name:     String,
  val nameKind: NameKind,
  val tpe:      T,
  clock:        C,
  reset:        R,
  init:         I,
  val refer:    MlirValue)
    extends Referable[T]
    with Named
