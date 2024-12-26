// SPDX-License-Identifier: Apache-2.0
package me.jiuyang.zaozi.circtlib.tests

import me.jiuyang.zaozi.circtlib.*
import utest.*

object Smoke extends TestSuite:
  val tests = Tests:
    test("Passthrough"):
      val name:    String       = "Passthrough"
      val handler: CirctHandler = new CirctHandler
      val root:    MlirModule   = handler.mlirModuleCreateEmpty(handler.unkLoc)

      // create a circuit.
      val mlirCircuit: CirctHandler#Op = handler
        .OpBuilder("firrtl.circuit", handler.mlirModuleGetBody(root), handler.unkLoc)
        .withRegion(Seq((Seq.empty, Seq.empty)))
        .withNamedAttr("name", handler.mlirStringAttrGet(name))
        .withNamedAttr("rawAnnotations", handler.firrtlImportAnnotationsFromJSONRaw("[]").get)
        .withNamedAttr("annotations", handler.emptyArrayAttr)
        .build()

      // create a module
      val ports = Ports(
        names = Seq("i", "o"),
        types = Seq(handler.firrtlTypeGetUInt(32), handler.firrtlTypeGetUInt(32)),
        dirs = Seq(FIRRTLDirection.In, FIRRTLDirection.Out),
        locs = Seq(handler.unkLoc, handler.unkLoc)
      )

      val mlirModule: CirctHandler#Op =
        handler
          .OpBuilder("firrtl.module", mlirCircuit.region(0).block(0), handler.unkLoc)
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

      // create the module contents.
      val i:       MlirValue       = handler.mlirBlockGetArgument(mlirModule.region(0).block(0), 0)
      val o:       MlirValue       = handler.mlirBlockGetArgument(mlirModule.region(0).block(0), 1)
      val connect: CirctHandler#Op = handler
        .OpBuilder("firrtl.connect", mlirModule.region(0).block(0), handler.unkLoc)
        .withOperand( /* dest */ o)
        .withOperand( /* src */ i)
        .build()

      // match result
      val out = new StringBuilder
      handler.mlirExportFIRRTL(root, out ++= _)
      assert(out.toString.contains("""circuit Passthrough :
                                     |  public module Passthrough :
                                     |    input i : UInt<32>
                                     |    output o : UInt<32>
                                     |
                                     |    connect o, i
                                     |""".stripMargin))
