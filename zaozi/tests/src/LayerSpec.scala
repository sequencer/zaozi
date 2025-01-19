// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 <liu@jiuyang.me>
package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.circt.scalalib.firrtl.capi.{
  given_DialectHandleApi,
  given_FirtoolOptionsApi,
  given_PassManagerApi,
  FirtoolOptions,
  FirtoolOptionsApi
}
import org.llvm.mlir.scalalib.{
  given_ContextApi,
  given_PassManagerApi,
  Block,
  Context,
  ContextApi,
  PassManager,
  PassManagerApi
}
import utest.*

import java.lang.foreign.Arena

case class LayerSpecParameter(width: Int, moduleName: String, layers: Seq[Layer]) extends Parameter

class LayerSpecIO(parameter: LayerSpecParameter) extends HWInterface[LayerSpecParameter](parameter):
  val a0     = Flipped(UInt(parameter.width.W))
  val a0b0   = Flipped(UInt(parameter.width.W))
  val a0b0c0 = Flipped(UInt(parameter.width.W))
  val a0b1   = Flipped(UInt(parameter.width.W))

class LayerSpecProbe(parameter: LayerSpecParameter) extends DVInterface[LayerSpecParameter](parameter):
  val a0     = ProbeRead(UInt(parameter.width.W), parameter.getLayers("A0"))
  val a0b0   = ProbeRead(UInt(parameter.width.W), parameter.getLayers("A0")("A0B0"))
  val a0b0c0 = ProbeRead(UInt(parameter.width.W), parameter.getLayers("A0")("A0B0")("A0B0C0"))
  val a0b1   = ProbeRead(UInt(parameter.width.W), parameter.getLayers("A0")("A0B1"))

object LayerSpec extends TestSuite:
  val tests = Tests:
    test("Simple Layer"):
      val parameter = LayerSpecParameter(
        32,
        "SimpleLayerModule",
        Seq(
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
      )
      verilogTest(parameter, LayerSpecIO(parameter), LayerSpecProbe(parameter))(
        "bind SimpleLayerModule SimpleLayerModule_A0 a0_0",
        "bind SimpleLayerModule SimpleLayerModule_A0_A0B1 a0_a0B1",
        "bind SimpleLayerModule SimpleLayerModule_A0_A0B0_A0B0C0 a0_a0B0_a0B0C0",
        "bind SimpleLayerModule SimpleLayerModule_A0_A0B0 a0_a0B0"
      ):
        val p     = summon[LayerSpecParameter]
        val io    = summon[Interface[LayerSpecIO]]
        val probe = summon[Interface[LayerSpecProbe]]
        layer("A0"):
          probe.a0 <== io.a0
          layer("A0B0"):
            probe.a0b0 <== io.a0b0
            layer("A0B0C0"):
              probe.a0b0c0 <== io.a0b0c0
          layer("A0B1"):
            probe.a0b1 <== io.a0b1
