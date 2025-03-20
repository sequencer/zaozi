// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Yuhang Zeng <unlsycn@unlsycn.com>
package me.jiuyang.zaozi.circtlib.tests

import org.llvm.circt.scalalib.emit.capi.given_DialectHandleApi
import org.llvm.circt.scalalib.firrtl.capi.given_DialectHandleApi
import org.llvm.circt.scalalib.hw.capi.given_AttributeApi
import org.llvm.circt.scalalib.om.capi.{*, given}
import org.llvm.mlir.scalalib.{Module as MlirModule, ModuleApi as MlirModuleApi, *, given}

import java.lang.foreign.Arena
import utest.*

object OmSmoke extends TestSuite:
  val tests = Tests:
    val arena     = Arena.ofConfined()
    given Arena   = arena
    val context   = summon[ContextApi].contextCreate
    context.loadOmDialect()
    // for mlirbc parsing
    context.loadFirrtlDialect()
    context.loadEmitDialect()
    context.allowUnregisteredDialects(true)
    given Context = context
    test("Load OM from mlirbc"):
      val mlirbcFile = os.pwd / "gcd.mlirbc"
      os.proc(
        "firtool",
        s"${sys.env.get("MILL_TEST_RESOURCE_DIR").get}/gcd.mlir",
        "--emit-bytecode",
        s"--output-final-mlir=${mlirbcFile}"
      ).call()
      val module     =
        summon[MlirModuleApi].moduleCreateParse(os.read.bytes(mlirbcFile))
      val evaluator  = summon[EvaluatorApi].evaluatorNew(module)
      val gcdClass   = evaluator.instantiate("GCD_Class", summon[EvaluatorValueApi].basePathGetEmpty)
      val width      = gcdClass
        .objectGetField(gcdClass.objectGetFieldNames.arrayAttrGetElement((0)))
        .objectGetField("width")

      width.isPrimitive ==> true
      width.getPrimitive.isIntegerAttr ==> true
      width.getPrimitive.integerAttrGetInt.integerAttrGetValueInt ==> 16

    test("EvaluatorValue Types"):
      val module    =
        summon[MlirModuleApi].moduleCreateParse(
          os.read(os.Path(s"${sys.env.get("MILL_TEST_RESOURCE_DIR").get}/value.mlir"))
        )
      val evaluator = summon[EvaluatorApi].evaluatorNew(module)
      test("Object"):
        val thingy = evaluator.instantiate(
          "Thingy",
          4.integerAttrGet(8.integerTypeGet).toEvaluatorValue,
          8.integerAttrGet(32.integerTypeGet).toEvaluatorValue
        )

        thingy.isObject ==> true
        thingy.objectGetType.isClassType ==> true
        thingy.objectGetType.classTypeGetName.str ==> "Thingy"

        val widget = thingy.objectGetField("widget")
        val gadget = thingy.objectGetField("gadget")

        test("No guarantee of the order of the field names"):
          val fieldNames = thingy.objectGetFieldNames
          Seq
            .tabulate(fieldNames.arrayAttrGetNumElements)(i => fieldNames.arrayAttrGetElement(i).stringAttrGetValue)
            .toSet ==> Set(
            "widget",
            "gadget",
            "blue_1",
            "blue_2"
          )

        widget.isObject ==> true
        gadget.isObject ==> true

        test("MLIR IntegerAttr"):
          val widgetBlue1 = widget.objectGetField("blue_1")
          widgetBlue1.isPrimitive ==> true
          widgetBlue1.getPrimitive.isIntegerAttr ==> false
          widgetBlue1.getPrimitive.isInteger ==> true
          widgetBlue1.getPrimitive.integerAttrGetValueInt ==> 5

        test("Nested Fields"):
          val nestFieldClass = evaluator.instantiate("NestedField4")
          nestFieldClass.objectGetField("result").getPrimitive.boolAttrGetValue ==> true

      test("Discardable Attribute"):
        val discardableClass =
          evaluator.instantiate("DiscardableAttrs")
        discardableClass.objectGetFieldNames.arrayAttrGetNumElements ==> 0

      test("Reference Constant"):
        val refClass = evaluator.instantiate("ReferenceConstant")

        val myrefAttr = refClass.objectGetField("myref").getPrimitive
        val symAttr   = refClass.objectGetField("sym").getPrimitive

        // TODO: add CAPI for SymbolRefAttr in CIRCT
        myrefAttr.isReferenceAttr ==> true

        myrefAttr.referenceAttrGetInnerRef.innerRefAttrGetModule.stringAttrGetValue ==> "A"
        myrefAttr.referenceAttrGetInnerRef.innerRefAttrGetName.stringAttrGetValue ==> "inst_1"

      test("List"):
        test("List Constant"):
          val listClass = evaluator.instantiate("ListConstant")
          val listI64   = listClass.objectGetField("list_i64")
          val listI32   = listClass.objectGetField("list_i32")

          listI64.isList ==> false
          listI32.isList ==> false

          val listI64Attr = listI64.getPrimitive
          val listI32Attr = listI32.getPrimitive

          listI64Attr.isListAttr ==> true
          listI32Attr.isListAttr ==> true
          listI64Attr.listAttrGetElement(0).integerAttrGetValueInt ==> 42
          listI32Attr.listAttrGetNumElements ==> 0

        test("OM List"):
          val listCreateClass = evaluator.instantiate("ListCreate")
          val listField       = listCreateClass.objectGetField("list_field")

          listField.isList ==> true
          listField.listGetNumElements ==> 2
          listField.listGetElement(0).objectGetField("blue_1").getPrimitive.integerAttrGetValueInt ==> 5

      test("Integer Constant"):
        val intClass = evaluator.instantiate("IntegerConstant")
        val intAttr  = intClass.objectGetField(intClass.objectGetFieldNames.arrayAttrGetElement(0)).getPrimitive

        intAttr.isIntegerAttr ==> true
        intAttr.integerAttrGetInt.integerAttrGetValueInt ==> 8428132854L

      test("String Constant"):
        val stringClass = evaluator.instantiate("StringConstant")
        val stringAttr  = stringClass.objectGetField("string").getPrimitive

        stringAttr.isString ==> true
        stringAttr.stringAttrGetValue ==> "foo"

      test("Bool Constant"):
        val boolClass                            = evaluator.instantiate("BoolConstant", true.boolAttrGet.toEvaluatorValue)
        val Seq(bool1Attr, bool2Attr, bool3Attr) =
          Seq("bool", "bool2", "bool3").map(name => boolClass.objectGetField(name).getPrimitive)

        bool1Attr.isBool ==> true
        bool1Attr.boolAttrGetValue ==> true
        bool2Attr.boolAttrGetValue ==> true
        bool3Attr.boolAttrGetValue ==> false

      test("Map"):
        test("Map Constant"):
          val mapClass = evaluator.instantiate("MapConstant")
          val mapI64   = mapClass.objectGetField("map_i64")

          mapI64.isMap ==> false
          mapI64.getPrimitive.isMapAttr ==> true

          val mapI64Attr = mapI64.getPrimitive

          mapI64Attr.mapAttrGetNumElements ==> 2
          mapI64Attr.mapAttrGetElementKey(0).str ==> "a"
          mapI64Attr.mapAttrGetElementValue(1).integerAttrGetValueInt ==> 32

        test("OM Map"):
          val mapCreateClass =
            evaluator.instantiate("MapCreate")
          val mapField       = mapCreateClass.objectGetField("map_field")

          mapField.isMap ==> true

          val keys = mapField.mapGetKeys
          keys.arrayAttrGetNumElements ==> 2
          mapField.mapGetElement(keys.arrayAttrGetElement(0)).isObject ==> true
          mapField.mapGetType.isMapType ==> true
          mapField.mapGetType.mapTypeGetKeyType.isStringType ==> true

      test("Tuple"):
        val tupleClass = evaluator.instantiate("Tuple", true.boolAttrGet.toEvaluatorValue)
        val tuple      = tupleClass.objectGetField("tuple")
        val value      = tupleClass.objectGetField("val")

        tuple.isTuple ==> true
        tuple.tupleGetElement(0).getPrimitive.boolAttrGetValue ==> true
        tuple.tupleGetElement(1).getPrimitive.stringAttrGetValue ==> value.getPrimitive.stringAttrGetValue

      test("FrozenPath"):
        val pathClass = evaluator.instantiate("FrozenPath", summon[EvaluatorValueApi].basePathGetEmpty)
        test("FrozenPath"):
          val path      = pathClass.objectGetField("path")
          val pathEmpty = pathClass.objectGetField("path_empty")

          pathEmpty.isPath ==> true
          path.pathGetAsString.stringAttrGetValue ==> "OMReferenceTarget:~Foo|Foo/bar:Bar>w.a"

        test("FrozenBasePath"):
          val basepath = pathClass.objectGetField("basepath")

          basepath.isBasePath ==> true

      test("Any"):
        test("Any Type will preserve the original type"):
          val anyClass = evaluator.instantiate("Any")
          val objField = anyClass.objectGetField("object")
          val strField = anyClass.objectGetField("string")

          objField.isObject ==> true
          strField.isPrimitive ==> true
          strField.getPrimitive.stringAttrGetValue ==> "foo"

      test("with Object Field"):
        val objectFieldClass = evaluator.instantiate("ObjectField")
        objectFieldClass.objectGetField("field").isObject ==> true

      test("Nested Reference Value"):
        val outerClass = evaluator.instantiate("OuterClass1")
        outerClass
          .objectGetField("om")
          .objectGetField("any_list1")
          .listGetElement(0)
          .objectGetField("any_list2")
          .listGetElement(0)
          .isObject ==> true
