// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.circt.scalalib.firrtl.capi.{FirtoolOptions, FirtoolOptionsApi, given_DialectHandleApi, given_FirtoolOptionsApi, given_PassManagerApi}
import org.llvm.mlir.scalalib.{Context, ContextApi, PassManager, PassManagerApi, given_ContextApi, given_PassManagerApi}
import utest.*

import java.lang.foreign.Arena

object ExportVerilog extends TestSuite:
  val tests = Tests:
    val parameter = SimpleParameter(32, "PassthroughModule")
    val out       = new StringBuilder
    test("Passthrough"):
      verilogTest(parameter, PassthroughInterface(parameter))(
        "assign o = i;"
      ): (p: SimpleParameter, io: Wire[PassthroughInterface]) =>
        io.o := io.i
