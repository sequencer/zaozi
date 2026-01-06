// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 <liu@jiuyang.me>
package me.jiuyang.zaozitest

import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import me.jiuyang.zaozi.testlib.*

import org.llvm.mlir.scalalib.capi.ir.{given_ContextApi, Block, Context, ContextApi}
import org.llvm.mlir.scalalib.capi.pass.{given_PassManagerApi, PassManager, PassManagerApi}
import utest.{test, TestSuite, Tests}

import java.lang.foreign.Arena
import scala.annotation.meta.param

case class SVASpecParameter(width: Int) extends Parameter
given upickle.default.ReadWriter[SVASpecParameter] = upickle.default.macroRW

class SVASpecLayers(parameter: SVASpecParameter) extends LayerInterface(parameter):
  def layers = Seq(
    Layer(
      "Assertion"
    )
  )

class SVASpecIO(parameter: SVASpecParameter) extends HWBundle(parameter):
  val ib0 = Flipped(Bool())
  val ib1 = Flipped(Bool())

class SVASpecProbe(parameter: SVASpecParameter) extends DVBundle[SVASpecParameter, SVASpecLayers](parameter)

object SVASpec extends TestSuite:
  val tests = Tests:
    test("Simple SVA"):
      @generator
      object SimpleSVA extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe] with HasVerilogTest:
        def architecture(parameter: SVASpecParameter) =
          val io    = summon[Interface[SVASpecIO]]
          val probe = summon[Interface[SVASpecProbe]]
          val a:    Referable[Bool] & HasOperation = io.ib0
          val seq:  Sequence                       = a.S
          val prop: Property                       = seq.P

          assert(property = prop, label = Some("Simple SVA"))

      val moduleName = SimpleSVA.moduleName(SVASpecParameter(32))
      SimpleSVA.verilogTest(SVASpecParameter(32))(
        s"Simple_SVA: assert property (disable iff (_GEN) ib0);"
      )

    test("api"):
      test("assert"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a: Referable[Bool] & HasOperation = io.ib0

            assert(property = a.S.P, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"assert_0: assert property (disable iff (_GEN) ib0);"
        )

      test("assume"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a: Referable[Bool] & HasOperation = io.ib0

            assume(property = a.S.P, label = Some("assume"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"assume_0: assume property (disable iff (_GEN) ib0);"
        )

      test("cover"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a: Referable[Bool] & HasOperation = io.ib0

            cover(property = a.S.P, label = Some("cover"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"cover_0: cover property (disable iff (_GEN) ib0);"
        )

    test("Sequence"):
      test("##n"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:       Referable[Bool] & HasOperation = io.ib0
            val b:       Referable[Bool] & HasOperation = io.ib1
            val as:      Sequence                       = a.S
            val bs:      Sequence                       = b.S
            val delayed: Sequence                       = as.##(1)(bs)

            assert(property = delayed.P, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"ib0 ##1 ib1"
        )

      test("##[n:m]"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:       Referable[Bool] & HasOperation = io.ib0
            val b:       Referable[Bool] & HasOperation = io.ib1
            val as:      Sequence                       = a.S
            val bs:      Sequence                       = b.S
            val delayed: Sequence                       = as.##(1, Some(2))(bs)

            assert(property = delayed.P, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"ib0 ##[1:2] ib1"
        )

      test("##[+]"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:        Referable[Bool] & HasOperation = io.ib0
            val b:        Referable[Bool] & HasOperation = io.ib1
            val as:       Sequence                       = a.S
            val bs:       Sequence                       = b.S
            val delayed0: Sequence                       = as.##(1, None)(bs)
            val delayed1: Sequence                       = as ##+ bs

            assert(property = delayed0.P, label = Some("assert0"))
            assert(property = delayed1.P, label = Some("assert1"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"assert0: assert property (disable iff (_GEN) ib0 ##[+] ib1);",
          s"assert1: assert property (disable iff (_GEN) ib0 ##[+] ib1);"
        )

      test("##[*]"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:        Referable[Bool] & HasOperation = io.ib0
            val b:        Referable[Bool] & HasOperation = io.ib1
            val as:       Sequence                       = a.S
            val bs:       Sequence                       = b.S
            val delayed0: Sequence                       = as.##(0, None)(bs)
            val delayed1: Sequence                       = as ##* bs

            assert(property = delayed0.P, label = Some("assert0"))
            assert(property = delayed1.P, label = Some("assert1"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"assert0: assert property (disable iff (_GEN) ib0 ##[*] ib1);",
          s"assert1: assert property (disable iff (_GEN) ib0 ##[*] ib1);"
        )

      test("[*n]"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:       Referable[Bool] & HasOperation = io.ib0
            val seq:     Sequence                       = a.S
            val delayed: Sequence                       = seq * 1

            assert(property = delayed.P, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"ib0[*1]"
        )

      test("[*n:m]"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:   Referable[Bool] & HasOperation = io.ib0
            val seq: Sequence                       = a.S
            val rep: Sequence                       = seq.*(1, Some(2))

            assert(property = rep.P, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"ib0[*1:2]"
        )

      test("[*n:$]"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val seq:  Sequence                       = a.S
            val rep0: Sequence                       = seq.*(0, None) // [*0:$] -> [*]
            val rep1: Sequence                       = seq.*(1, None) // [*1:$] -> [+]
            val rep2: Sequence                       = seq.*(2, None) // [*2:$] -> [*2:$]

            assert(property = rep0.P, label = Some("assert0"))
            assert(property = rep1.P, label = Some("assert1"))
            assert(property = rep2.P, label = Some("assert2"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"assert0: assert property (disable iff (_GEN) ib0[*]);",
          s"assert1: assert property (disable iff (_GEN) ib0[+]);",
          s"assert2: assert property (disable iff (_GEN) ib0[*2:$$]);"
        )

      test("[->n:m]"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val seq:  Sequence                       = a.S
            val prop: Property                       = seq.*->(1, 2).P

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"ib0[->1:2]"
        )

      test("[=n:m]"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val seq:  Sequence                       = a.S
            val prop: Property                       = seq.*=(1, 2).P

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"ib0[=1:2]"
        )

      test("and"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val prop: Property                       = as.and(bs).P

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"ib0 & ib1"
        )

      test("intersect"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S * 3
            val bs:   Sequence                       = b.S * 2
            val prop: Property                       = as.intersect(bs).P

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"ib0[*3] intersect ib1[*2]"
        )

      test("or"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val prop: Property                       = as.or(bs).P

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"ib0 | ib1"
        )

      test("throughout"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val bs:   Sequence                       = b.S
            val prop: Property                       = a.throughout(bs).P

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"ib0[*] intersect ib1"
        )

      test("within"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val prop: Property                       = as.within(bs).P

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"1'h1 ##[*] ib0 ##[*] 1'h1 intersect ib1"
        )

    test("Property"):
      test("|->"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val ap:   Property                       = as.P
            val bp:   Property                       = bs.P
            val prop: Property                       = as |-> bp

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"ib0 |-> ib1"
        )
      test("|=>"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val ap:   Property                       = as.P
            val bp:   Property                       = bs.P
            val prop: Property                       = as |=> bp

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"ib0 |=> ib1"
        )
      test("implies"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val ap:   Property                       = as.P
            val bp:   Property                       = bs.P
            val prop: Property                       = ap.implies(bp)

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"not ib0 or ib1"
        )
      test("iff"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val ap:   Property                       = as.P
            val bp:   Property                       = bs.P
            val prop: Property                       = ap.iff(bp)

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"not ib0 | ib1 or ib0 & ib1"
        )
      test("#-#"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val ap:   Property                       = as.P
            val bp:   Property                       = bs.P
            val prop: Property                       = as #-# bp

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"not (ib0 |-> not ib1)"
        )
      test("#=#"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val ap:   Property                       = as.P
            val bp:   Property                       = bs.P
            val prop: Property                       = as #=# bp

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"assert property (disable iff (_GEN) not (ib0 |-> not ib1) and not (ib1 |-> not ib0)"
        )
      test("nextTime"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val ap:   Property                       = as.P
            val bp:   Property                       = bs.P
            val prop: Property                       = ap.nextTime

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"##1 ib0"
        )
      test("nextTime[n]"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val ap:   Property                       = as.P
            val bp:   Property                       = bs.P
            val prop: Property                       = ap.nextTime(2)

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"##2 ib0"
        )
      test("always"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val ap:   Property                       = as.P
            val bp:   Property                       = bs.P
            val prop: Property                       = ap.always

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"ib0[*]"
        )
      test("always[n:m]"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val ap:   Property                       = as.P
            val bp:   Property                       = bs.P
            val prop: Property                       = ap.always(2, 3)

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"ib0[*2:3]"
        )
      test("eventually"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val ap:   Property                       = as.P
            val bp:   Property                       = bs.P
            val prop: Property                       = ap.eventually

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"s_eventually ib0"
        )
      test("until"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val ap:   Property                       = as.P
            val bp:   Property                       = bs.P
            val prop: Property                       = ap.until(bp)

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"ib0 until ib1"
        )
      test("untilWith"):
        @generator
        object SimpleSVA
            extends Generator[SVASpecParameter, SVASpecLayers, SVASpecIO, SVASpecProbe]
            with HasVerilogTest:
          def architecture(parameter: SVASpecParameter) =
            val io = summon[Interface[SVASpecIO]]
            val a:    Referable[Bool] & HasOperation = io.ib0
            val b:    Referable[Bool] & HasOperation = io.ib1
            val as:   Sequence                       = a.S
            val bs:   Sequence                       = b.S
            val ap:   Property                       = as.P
            val bp:   Property                       = bs.P
            val prop: Property                       = ap.untilWith(bp)

            assert(property = prop, label = Some("assert"))
        SimpleSVA.verilogTest(SVASpecParameter(32))(
          s"not (ib0 until ib1) or ib0 & ib1"
        )
