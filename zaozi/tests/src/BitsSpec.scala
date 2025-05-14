// // SPDX-License-Identifier: Apache-2.0
// // SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
// package me.jiuyang.zaozi.tests

// import me.jiuyang.zaozi.*
// import me.jiuyang.zaozi.default.{*, given}
// import me.jiuyang.zaozi.reftpe.*

// import org.llvm.circt.scalalib.firrtl.capi.given_DialectHandleApi
// import org.llvm.mlir.scalalib.{given_ContextApi, Context, ContextApi}

// import java.lang.foreign.Arena
// import utest.*
// import me.jiuyang.zaozi.magic.macros.generator

// case class BitsSpecParameter(width: Int) extends Parameter:
//   def moduleName: String     = "BitsSpecModule"
//   def layers:     Seq[Layer] = Nil
// class BitsSpecIO(
//   parameter: BitsSpecParameter)
//     extends HWInterface[BitsSpecParameter](parameter):
//   val a          = Flipped(Bits(parameter.width.W))
//   val bits       = Aligned(Bits(parameter.width.W))
//   val asyncReset = Flipped(AsyncReset())

// class BitsSpecProbe(
//   parameter: BitsSpecParameter)
//     extends DVInterface[BitsSpecParameter](parameter)

// object BitsSpec extends TestSuite:
//   val tests = Tests:
//     test("ExtractRange"):
//       test("ExtractRange"):
//         @generator
//         object ExtractRange extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasFirrtlTest:
//           def architecture(parameter: BitsSpecParameter) =
//             val io = summon[Interface[BitsSpecIO]]
//             io.bits := io.a.bits(4, 3)
//         ExtractRange.firrtlTest(BitsSpecParameter(8))(
//           "node _GEN_0 = bits(io.a, 4, 3)"
//         )
//       test("ExtractRange apply"):
//         @generator
//         object ExtractRangeApply extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasFirrtlTest:
//           def architecture(parameter: BitsSpecParameter) =
//             val io = summon[Interface[BitsSpecIO]]
//             io.bits := io.a(4, 3)
//         ExtractRangeApply.firrtlTest(BitsSpecParameter(8))(
//           "node _GEN_0 = bits(io.a, 4, 3)"
//         )
//       test("Named ExtractRange apply"):
//         @generator
//         object NamedExtractRangeApply
//             extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe]
//             with HasFirrtlTest:
//           def architecture(parameter: BitsSpecParameter) =
//             val io = summon[Interface[BitsSpecIO]]
//             io.bits := io.a(lo = 3, hi = 4)
//         NamedExtractRangeApply.firrtlTest(BitsSpecParameter(8))(
//           "node _GEN_0 = bits(io.a, 4, 3)"
//         )
//       test("ExtractElement"):
//         @generator
//         object ExtractElement extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasFirrtlTest:
//           def architecture(parameter: BitsSpecParameter) =
//             val io = summon[Interface[BitsSpecIO]]
//             io.bits := io.a.bit(4)
//         ExtractElement.firrtlTest(BitsSpecParameter(8))(
//           "node _GEN_0 = bits(io.a, 4, 4)"
//         )
//       test("ExtractElement apply"):
//         @generator
//         object ExtractElementApply extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe] with HasFirrtlTest:
//           def architecture(parameter: BitsSpecParameter) =
//             val io = summon[Interface[BitsSpecIO]]
//             io.bits := io.a(4)
//         ExtractElementApply.firrtlTest(BitsSpecParameter(8))(
//           "node _GEN_0 = bits(io.a, 4, 4)"
//         )
//       test("Named ExtractElement apply"):
//         @generator
//         object NamedExtractElementApply
//             extends Generator[BitsSpecParameter, BitsSpecIO, BitsSpecProbe]
//             with HasFirrtlTest:
//           def architecture(parameter: BitsSpecParameter) =
//             val io = summon[Interface[BitsSpecIO]]
//             io.bits := io.a(idx = 4)
//         NamedExtractElementApply.firrtlTest(BitsSpecParameter(8))(
//           "node _GEN_0 = bits(io.a, 4, 4)"
//         )
