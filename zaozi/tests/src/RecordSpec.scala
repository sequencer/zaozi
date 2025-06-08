// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozitest

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.Interface
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.mlir.scalalib.capi.ir.{given_ContextApi, Context, ContextApi}
import utest.*

import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.Block
import me.jiuyang.zaozi.reftpe.Referable

class UnfixedFieldsNumRecord(n: Int, width: Int) extends Record:
  val inputs  = Seq.tabulate(n)(i => Flipped(s"input_$i", UInt(width.W)))
  val outputs = Seq.tabulate(n)(i => Aligned(s"output_$i", UInt(width.W)))

class SimpleRecord(width: Int) extends Record:
  val i = Flipped("a", UInt(width.W))
  val o = Aligned("b", UInt(width.W))

class NestedRecord(width: Int) extends Record:
  val inner = Aligned("inner", new SimpleRecord(width))

case class RecordSpecParameter(fieldNum: Int, width: Int) extends Parameter
given upickle.default.ReadWriter[RecordSpecParameter] = upickle.default.macroRW

class RecordSpecLayers(parameter: RecordSpecParameter) extends LayerInterface(parameter)

class DynamicFieldsNumIO(parameter: RecordSpecParameter) extends HWBundle(parameter):
  val a = Aligned(new UnfixedFieldsNumRecord(parameter.fieldNum, parameter.width))

class NestedRecordIO(parameter: RecordSpecParameter) extends HWBundle(parameter):
  val b = Aligned(new NestedRecord(parameter.width))

class SimpleRecordIO(parameter: RecordSpecParameter) extends HWBundle(parameter):
  val c = Aligned(new SimpleRecord(parameter.width))

class RecordSpecProbe(parameter: RecordSpecParameter) extends DVBundle[RecordSpecParameter, RecordSpecLayers](parameter)

object RecordSpec extends TestSuite:
  val tests = Tests:
    test("Dynamic fields num"):
      @generator
      object DynamicFieldsNum
          extends Generator[RecordSpecParameter, RecordSpecLayers, DynamicFieldsNumIO, RecordSpecProbe]
          with HasVerilogTest:
        def architecture(parameter: RecordSpecParameter) =
          val io = summon[Interface[DynamicFieldsNumIO]]
          Seq.tabulate(parameter.fieldNum): i =>
            io.a.field(s"output_$i") := io.a.field(s"input_$i")
      DynamicFieldsNum.verilogTest(RecordSpecParameter(2, 32))(
        "assign a_output_0 = a_input_0;",
        "assign a_output_1 = a_input_1;"
      )

    test("Nested Record"):
      @generator
      object NestedRecordTest
          extends Generator[RecordSpecParameter, RecordSpecLayers, NestedRecordIO, RecordSpecProbe]
          with HasVerilogTest:
        def architecture(parameter: RecordSpecParameter) =
          val io = summon[Interface[NestedRecordIO]]
          io.b.field[Record]("inner").field("b") := io.b.field[Record]("inner").field("a")
      NestedRecordTest.verilogTest(RecordSpecParameter(2, 32))(
        "assign b_inner_b = b_inner_a;"
      )

    test("Fields cannot access by val name"):
      @generator
      object AccessValName
          extends Generator[RecordSpecParameter, RecordSpecLayers, SimpleRecordIO, RecordSpecProbe]
          with HasCompileErrorTest:
        def architecture(parameter: RecordSpecParameter) =
          val io = summon[Interface[SimpleRecordIO]]
          intercept[Exception]:
            io.c.field("o") := io.c.field("i")
          .getMessage() ==> "o not found in ArrayBuffer(a, b)"
      AccessValName.compileErrorTest(RecordSpecParameter(2, 32))
