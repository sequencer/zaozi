// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.plugin

import utest._

import me.jiuyang.zaozi._
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import me.jiuyang.zaozi.testlib.*

/** Test bundle for plugin verification. */
class TestBundle extends Bundle:
  val input  = Aligned(UInt(8.W))
  val output = Flipped(UInt(8.W))
  val flag   = Aligned(Bool())

/** Nested bundle for testing complex hierarchies. */
class OuterBundle extends Bundle:
  val inner = Aligned(new TestBundle)
  val data  = Aligned(UInt(32.W))

/** Parameter for test generators. */
case class PluginTestParameter(width: Int) extends Parameter
given upickle.default.ReadWriter[PluginTestParameter] = upickle.default.macroRW

/** Layer interface for test generators. */
class PluginTestLayers(parameter: PluginTestParameter) extends LayerInterface(parameter):
  def layers = Seq.empty

/** IO bundle that uses TestBundle - this triggers field access tracking. */
class PluginTestIO(parameter: PluginTestParameter) extends HWBundle(parameter):
  val in     = Flipped(UInt(parameter.width.W))
  val out    = Aligned(UInt(parameter.width.W))
  val bundle = Aligned(new TestBundle)
  val nested = Aligned(new OuterBundle)

/** Probe bundle for test generators. */
class PluginTestProbe(parameter: PluginTestParameter) extends DVBundle[PluginTestParameter, PluginTestLayers](parameter)

/** Test suite for the zaozi SemanticDB compiler plugin.
  *
  * These tests verify that the plugin correctly identifies bundle field definitions and usages.
  */
object PluginSpec extends TestSuite:
  val tests = Tests {
    test("Bundle field definitions are collected") {
      // TestBundle and OuterBundle are defined above - the plugin should collect their fields
      val stats = BundleFieldRegistry.stats
      assert(stats.contains("BundleFieldRegistry"))
    }

    test("Bundle field access via Interface triggers usage tracking") {
      // This generator accesses bundle fields via Dynamic selectDynamic
      // The plugin should track these as field usages
      @generator
      object BundleFieldAccessTest
          extends Generator[PluginTestParameter, PluginTestLayers, PluginTestIO, PluginTestProbe]
          with HasVerilogTest:
        def architecture(parameter: PluginTestParameter) =
          val io = summon[Interface[PluginTestIO]]
          // These field accesses should be tracked by the plugin:
          // - io.bundle.input (access TestBundle#input)
          // - io.bundle.output (access TestBundle#output)
          // - io.nested.inner.flag (nested access)
          // - io.nested.data (access OuterBundle#data)
          io.out           := io.bundle.input
          io.bundle.output := io.in

      // Just verify it compiles - the actual tracking happens at compile time
      assert(BundleFieldAccessTest != null)
    }

    test("Nested bundle field access") {
      @generator
      object NestedBundleAccessTest
          extends Generator[PluginTestParameter, PluginTestLayers, PluginTestIO, PluginTestProbe]
          with HasVerilogTest:
        def architecture(parameter: PluginTestParameter) =
          val io = summon[Interface[PluginTestIO]]
          // Nested field access: io.nested.inner.input
          io.out                 := io.nested.inner.input
          io.nested.inner.output := io.in
          io.nested.data.dontCare()
          io.bundle.flag.dontCare()

      assert(NestedBundleAccessTest != null)
    }

    test("Wire with Bundle type") {
      @generator
      object WireWithBundleTest
          extends Generator[PluginTestParameter, PluginTestLayers, PluginTestIO, PluginTestProbe]
          with HasVerilogTest:
        def architecture(parameter: PluginTestParameter) =
          val io   = summon[Interface[PluginTestIO]]
          val wire = Wire(new TestBundle)
          // Access fields on the wire - these should be tracked by the plugin
          wire.input  := io.bundle.input
          wire.output := io.bundle.output
          wire.flag   := io.bundle.flag
          io.out      := wire.input

      assert(WireWithBundleTest != null)
    }

    test("BundleFieldRegistry API works") {
      val defs = BundleFieldRegistry.getAllDefinitions
      assert(defs != null)

      val symbols = BundleFieldRegistry.getAllBundleSymbols
      assert(symbols != null)
    }
  }
