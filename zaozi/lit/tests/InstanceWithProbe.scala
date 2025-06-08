// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 <liu@jiuyang.me>

// DEFINE: %{test} = scala-cli --server=false --java-home=%JAVAHOME --extra-jars=%RUNCLASSPATH --scala-version=%SCALAVERSION -O="-experimental" --java-opt="--enable-native-access=ALL-UNNAMED" --java-opt="--enable-preview" --java-opt="-Djava.library.path=%JAVALIBRARYPATH" --main-class Outer %s --
// RUN: %{test} config %t.json --width 32
// RUN: %{test} design %t.json
// RUN: firtool Outer*.mlirbc --parse-only | FileCheck %s -check-prefix=MLIR
// RUN: rm %t.json *.mlirbc -f

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

import java.lang.foreign.Arena

val fooLayers = Seq(
  Layer(
    "A0",
    Seq(
      Layer(
        "A0B0",
        Seq(
          Layer(
            "A0B0C0"
          ),
          Layer(
            "A0B0C1"
          )
        )
      ),
      Layer("A0B1"),
      Layer("A0B2")
    )
  ),
  Layer("A1")
)

case class InnerParameter(width: Int) extends Parameter
given upickle.default.ReadWriter[InnerParameter] = upickle.default.macroRW

class InnerLayers(parameter: InnerParameter) extends LayerInterface(parameter):
  def layers = fooLayers

class InnerIO(parameter: InnerParameter) extends HWBundle(parameter):
  val a0     = Flipped(UInt(parameter.width.W))
  val a0b0   = Flipped(UInt(parameter.width.W))
  val a0b0c0 = Flipped(UInt(parameter.width.W))
  val a0b1   = Flipped(UInt(parameter.width.W))

class InnerProbe(parameter: InnerParameter) extends DVBundle[InnerParameter, InnerLayers](parameter):
  val a0     = ProbeRead(UInt(parameter.width.W), layers("A0"))
  val a0b0   = ProbeRead(UInt(parameter.width.W), layers("A0")("A0B0"))
  val a0b0c0 = ProbeRead(UInt(parameter.width.W), layers("A0")("A0B0")("A0B0C0"))
  val a0b1   = ProbeRead(UInt(parameter.width.W), layers("A0")("A0B1"))

@generator
object Inner extends Generator[InnerParameter, InnerLayers, InnerIO, InnerProbe]:
  def architecture(parameter: InnerParameter) =
    val io               = summon[Interface[InnerIO]]
    val probe            = summon[Interface[InnerProbe]]
    given Seq[LayerTree] = this.layers(parameter)
    layer("A0"):
      probe.a0 <== io.a0
      layer("A0B0"):
        probe.a0b0 <== io.a0b0
        layer("A0B0C0"):
          probe.a0b0c0 <== io.a0b0c0
      layer("A0B1"):
        probe.a0b1 <== io.a0b1

case class OuterParameter(width: Int) extends Parameter
given upickle.default.ReadWriter[OuterParameter] = upickle.default.macroRW

class OuterLayers(parameter: OuterParameter) extends LayerInterface(parameter):
  def layers = fooLayers

class OuterIO(parameter: OuterParameter) extends HWBundle(parameter):
  val a0     = Flipped(UInt(parameter.width.W))
  val a0b0   = Flipped(UInt(parameter.width.W))
  val a0b0c0 = Flipped(UInt(parameter.width.W))
  val a0b1   = Flipped(UInt(parameter.width.W))

class OuterProbe(parameter: OuterParameter) extends DVBundle[OuterParameter, OuterLayers](parameter)

@generator
object Outer extends Generator[OuterParameter, OuterLayers, OuterIO, OuterProbe]:
  def architecture(parameter: OuterParameter) =
    val io    = summon[Interface[OuterIO]]
    val probe = summon[Interface[OuterProbe]]

    // MLIR: %inner_a0, %inner_a0b0, %inner_a0b0c0, %inner_a0b1, %inner_a0_0, %inner_a0b0_1, %inner_a0b0c0_2, %inner_a0b1_3 = firrtl.instance inner interesting_name {layers = [@A0::@A0B0::@A0B0C0, @A0::@A0B0::@A0B0C1, @A0::@A0B1, @A0::@A0B2, @A1]} @Inner_7b2bb635(in a0: !firrtl.uint<32>, in a0b0: !firrtl.uint<32>, in a0b0c0: !firrtl.uint<32>, in a0b1: !firrtl.uint<32>, out a0: !firrtl.probe<uint<32>>, out a0b0: !firrtl.probe<uint<32>>, out a0b0c0: !firrtl.probe<uint<32>>, out a0b1: !firrtl.probe<uint<32>>)
    val inner = Inner.instantiate(InnerParameter(parameter.width))
    inner.io.a0     := io.a0
    inner.io.a0b0   := io.a0b0
    inner.io.a0b0c0 := io.a0b0c0
    inner.io.a0b1   := io.a0b1

    // TODO: add probe to probe define?
