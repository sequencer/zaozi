// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

// RUN: scala-cli --server=false --java-home=%JAVAHOME --extra-jars=%RUNCLASSPATH --scala-version=%SCALAVERSION -O="-experimental" --java-opt="--enable-native-access=ALL-UNNAMED" --java-opt="--enable-preview" --java-opt="-Djava.library.path=%JAVALIBRARYPATH" %s && firtool Passthrough*.mlirbc | FileCheck %s -check-prefix=VERILOG
// RUN: rm *.mlirbc

import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.circt.scalalib.capi.dialect.firrtl.DialectApi as FirrtlDialectApi
import org.llvm.circt.scalalib.capi.dialect.firrtl.given_DialectApi

import org.llvm.mlir.scalalib.{given_ContextApi, given_PassManagerApi, Context, ContextApi, PassManager, PassManagerApi}
import java.lang.foreign.Arena

case class PassthroughParameter(width: Int) extends Parameter
given upickle.default.ReadWriter[PassthroughParameter] = upickle.default.macroRW

class PassthroughLayers(parameter: PassthroughParameter) extends LayerInterface(parameter)

class PassthroughIO(parameter: PassthroughParameter) extends HWInterface(parameter):
  val i = Flipped(UInt(parameter.width.W))
  val o = Aligned(UInt(parameter.width.W))

class PassthroughProbe(parameter: PassthroughParameter)
    extends DVInterface[PassthroughParameter, PassthroughLayers](parameter)

@generator
object PassthroughModule extends Generator[PassthroughParameter, PassthroughLayers, PassthroughIO, PassthroughProbe]:
  // VERILOG-LABEL: module PassthroughModule_e88425e0(
  def architecture(parameter: PassthroughParameter) =
    // VERILOG-NEXT:   input  [31:0] i,
    // VERILOG-NEXT:   output [31:0] o
    // VERILOG-NEXT: );
    // VERILOG:   assign o = i;
    val io = summon[Interface[PassthroughIO]]
    io.o := io.i
  // VERILOG: endmodule

given Arena   = Arena.ofConfined()
given Context = summon[ContextApi].contextCreate
summon[FirrtlDialectApi].loadDialect

PassthroughModule.dumpMlirbc(PassthroughParameter(32))

summon[Context].destroy()
summon[Arena].close()
