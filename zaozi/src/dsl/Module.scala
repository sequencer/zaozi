// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.circtlib.{
  CirctHandler,
  FIRRTLConvention,
  FIRRTLDirection,
  MlirBlock,
  MlirLocation,
  MlirModule,
  MlirType,
  Ports
}
import me.jiuyang.zaozi.internal.{Context, NameKind}

trait Parameter
trait Interface[P <: Parameter](val parameter: P) extends Bundle
case class SourceLocator(file: sourcecode.File, line: sourcecode.Line):
  def toMLIR(
    using context: Context
  ): MlirLocation = toMLIR(context.handler)
  // TODO: wait for [[https://github.com/com-lihaoyi/sourcecode/issues/54]]
  def toMLIR(handler: CirctHandler): MlirLocation =
    handler.mlirLocationFileLineColGet(file.value, line.value, 0)

object Module:
  def apply[P <: Parameter, I <: Interface[P]](
    name:      String,
    parameter: P,
    interface: I
  )(body:      Context ?=> (P, Wire[I]) => Unit
  )(
    using
    file:      sourcecode.File,
    line:      sourcecode.Line
  ): Context =
    given context: Context = new Context:
      val parameter: Parameter    = parameter
      val handler:   CirctHandler = new CirctHandler
      val locator:   MlirLocation = SourceLocator(file, line).toMLIR(handler)
      val root:      MlirModule   = handler.mlirModuleCreateEmpty(locator)
      val elaboratedModule = collection.mutable.ArrayBuffer[String]()
      val mlirCircuit:  CirctHandler#Op                                        = handler
        .OpBuilder("firrtl.circuit", handler.mlirModuleGetBody(root), SourceLocator(file, line).toMLIR(handler))
        .withRegion(Seq((Seq.empty, Seq.empty)))
        .withNamedAttr("name", handler.mlirStringAttrGet(name))
        .withNamedAttr("rawAnnotations", handler.firrtlImportAnnotationsFromJSONRaw("[]").get)
        .withNamedAttr("annotations", handler.emptyArrayAttr)
        .build()
      val circuitBlock: MlirBlock                                              = mlirCircuit.region(0).block(0)
      // TODO: maybe detail source locator for port?
      val p:            Seq[(String, MlirType, FIRRTLDirection, MlirLocation)] = interface.firrtlType.fields.get.map(bf =>
        (bf.name, bf.tpe.toMLIR(handler), if (bf.isFlip) FIRRTLDirection.In else FIRRTLDirection.Out, locator)
      )

      val ports      = Ports(p.map(_._1), p.map(_._2), p.map(_._3), p.map(_._4))
      val mlirModule = handler
        .OpBuilder("firrtl.module", circuitBlock, locator)
        .withRegion(Seq((ports.types, ports.locs)))
        .withNamedAttr("sym_name", handler.mlirStringAttrGet(name))
        .withNamedAttr("sym_visibility", handler.mlirStringAttrGet("public"))
        .withNamedAttr("convention", handler.firrtlAttrGetConvention(FIRRTLConvention.Scalarized))
        .withNamedAttr("annotations", handler.emptyArrayAttr)
        .withNamedAttr("portDirections", ports.dirAttrs(handler))
        .withNamedAttr("portNames", ports.nameAttrs(handler))
        .withNamedAttr("portTypes", ports.typeAttrs(handler))
        .withNamedAttr("portAnnotations", ports.annotationAttrs(handler))
        .withNamedAttr("portSymbols", ports.symAttrs(handler))
        .withNamedAttr("portLocations", ports.locAttrs(handler))
        .build()
      val moduleBlock:   MlirBlock = mlirModule.region(0).block(0)
      val currentBlock:  MlirBlock = moduleBlock
      val interfaceWire: Wire[I]   = new Wire[I](
        s"io",
        NameKind.Droppable,
        interface,
        handler
          .OpBuilder("firrtl.wire", currentBlock, locator)
          .withNamedAttr("name", handler.mlirStringAttrGet("io"))
          .withNamedAttr(
            "nameKind",
            handler.firrtlAttrGetNameKind(me.jiuyang.zaozi.internal.toMLIR(NameKind.Droppable))
          )
          .withNamedAttr("annotations", handler.emptyArrayAttr)
          .withResult(
            interface.firrtlType
              .copy(fields = interface.firrtlType.fields.map(_.map(f => f.copy(isFlip = !f.isFlip))))
              .toMLIR(handler)
          )
          .build()
          .results
          .head
      )
      interfaceWire.tpe.elements.zipWithIndex.foreach:
        case (ele, idx) =>
          val io   = handler.mlirBlockGetArgument(moduleBlock, idx)
          val wire = handler
            .OpBuilder("firrtl.subfield", currentBlock, locator)
            .withNamedAttr("fieldIndex", handler.mlirIntegerAttrGet(handler.mlirIntegerTypeGet(32), idx))
            .withOperand( /* input */ interfaceWire.refer)
            .withResultInference(1)
            .build()
            .results
            .head
          if (ele.isFlip)
            handler
              .OpBuilder("firrtl.connect", currentBlock, locator)
              .withOperand( /* dest */ wire)
              .withOperand( /* src */ io)
              .build()
          else
            handler
              .OpBuilder("firrtl.connect", currentBlock, locator)
              .withOperand( /* dest */ io)
              .withOperand( /* src */ wire)
              .build()
    body(context.parameter.asInstanceOf[P], context.interfaceWire.asInstanceOf[Wire[I]])
    context
