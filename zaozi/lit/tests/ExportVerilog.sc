// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
// RUN: scala-cli --server=false --java-home=%JAVAHOME --extra-jars=%RUNCLASSPATH --scala-version=%SCALAVERSION --java-opt="--enable-native-access=ALL-UNNAMED" --java-opt="--enable-preview" --java-opt="-Djava.library.path=%JAVALIBRARYPATH" %s | FileCheck %s -check-prefix=VERILOG

import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.circt.scalalib.firrtl.capi.{FirtoolOptions, FirtoolOptionsApi, given_DialectHandleApi, given_FirtoolOptionsApi, given_PassManagerApi}
import org.llvm.mlir.scalalib.{Context, ContextApi, PassManager, PassManagerApi, given_ContextApi, given_PassManagerApi}
import me.jiuyang.zaozi.testutility.*
import java.lang.foreign.Arena

case class SimpleParameter(width: Int, moduleName: String) extends Parameter:
  def layers: Seq[Layer] = Seq.empty

class PassthroughIO(using SimpleParameter) extends HWInterface[SimpleParameter]:
  val i = Flipped(UInt(summon[SimpleParameter].width.W))
  val o = Aligned(UInt(summon[SimpleParameter].width.W))

class PassthroughProbe(using SimpleParameter) extends DVInterface[SimpleParameter]

// VERILOG-LABEL: module PassthroughModule(
given SimpleParameter(32, "PassthroughModule")
verilogTest(new PassthroughIO, new PassthroughProbe):
  // VERILOG-NEXT:   input  [31:0] i,
  // VERILOG-NEXT:   output [31:0] o
  // VERILOG-NEXT: );
    // VERILOG:   assign o = i;
  val io = summon[Interface[PassthroughIO]]
  io.o := io.i
// VERILOG: endmodule
