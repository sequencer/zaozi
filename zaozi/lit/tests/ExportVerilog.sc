// SPDX-License-Identifier: Apache-2.0
// RUN: scala-cli --server=false --java-home=%JAVAHOME --extra-jars=%RUNCLASSPATH --scala-version=%SCALAVERSION --java-opt="--enable-native-access=ALL-UNNAMED" --java-opt="--enable-preview" --java-opt="-Djava.library.path=%JAVALIBRARYPATH" %s | FileCheck %s -check-prefix=VERILOG

import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.circt.scalalib.firrtl.capi.{FirtoolOptions, FirtoolOptionsApi, given_DialectHandleApi, given_FirtoolOptionsApi, given_PassManagerApi}
import org.llvm.mlir.scalalib.{Context, ContextApi, PassManager, PassManagerApi, given_ContextApi, given_PassManagerApi}
import me.jiuyang.zaozi.testutility.*
import java.lang.foreign.Arena

case class SimpleParameter(width: Int, moduleName: String) extends Parameter

class PassthroughInterface(parameter: SimpleParameter) extends Interface[SimpleParameter](parameter):
  def moduleName: String = parameter.moduleName
  val i = Flipped(UInt(parameter.width.W))
  val o = Aligned(UInt(parameter.width.W))

// VERILOG-LABEL: module PassthroughModule(
val parameter = SimpleParameter(32, "PassthroughModule")
verilogTest(parameter, PassthroughInterface(parameter)):
  // VERILOG-NEXT:   input  [31:0] i,
  // VERILOG-NEXT:   output [31:0] o
  // VERILOG-NEXT: );
  (p: SimpleParameter, io: Wire[PassthroughInterface]) =>
    // VERILOG:   assign o = i;
    io.o := io.i
// VERILOG: endmodule
