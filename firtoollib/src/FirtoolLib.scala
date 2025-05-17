// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.firtoollib

import org.llvm.mlir.scalalib.Context
import os.Path
import org.llvm.mlir.scalalib.Module as MlirModule

import java.lang.foreign.Arena

/** A vertex of InstanceGraph.
  * @param moduleName
  *   the verilog name of this module.
  * @param children
  *   is a list of Module -> Instance name in String.
  */
case class InstanceGraphNode(moduleName: String, children: Seq[(InstanceGraphNode, String)])

/** The top of InstanceGraph. */
case class InstanceGraph(topLevelNodes: Seq[InstanceGraphNode])

enum PortDirection:
  case Input
  case Output
  case InOut
end PortDirection

/** A port that can map to SystemVerilog and IP-XACT. Only support scalar tpe for now.
  *
  * @note
  *   see ::circt::hw::PortInfo
  */
case class Port(name: String, width: Int, dir: PortDirection)

trait FirtoolApi:
  /** Parse mlir or mlirbc into [[MLIRModule]]. */
  def parseMlir(
    path: Path
  )(
    using Arena,
    Context
  ): MlirModule

  /** Parse mlir into [[MLIRModule]]. The output is in CHIRRTL Dialect, FIRRTL Dialect, HW Dialect.
    *
    * After parsing, you can use:
    *
    * [[org.llvm.circt.scalalib.firrtl.capi.PassManagerApi.populatePreprocessTransforms]]
    * [[org.llvm.circt.scalalib.firrtl.capi.PassManagerApi.populateCHIRRTLToLowFIRRTL]]
    * [[org.llvm.circt.scalalib.firrtl.capi.PassManagerApi.populateLowFIRRTLToHW]]
    *
    * to lower to HW Dialect.
    */
  def importFirrtl(
    path: Path
  )(
    using Arena,
    Context
  ): MlirModule

  /** Parse SystemVerilog into [[MlirModule]]. The output is in Moore Dialect.
    *
    * After parsing, you can use MooreToCore Conversion to lower to HW Dialect.
    */
  def importVerilog(
    paths: Seq[Path]
  )(
    using Arena,
    Context
  ): MlirModule

  /** Get Instance Graph from MLIR.
    * @param mlirModule
    *   should be lowered to HW or Firrtl Dialect.
    * @note
    *   see Dialect Interface: InstanceGraphModuleOpInterface and InstanceGraphInstanceOpInterface
    */
  def getInstanceGraph(
    mlirModule: MlirModule
  )(
    using Arena,
    Context
  ): InstanceGraph

  /** Get ports from the Top of HW Dialect.
    * @note
    *   see Dialect Interface PortList
    */
  def getPortList(
    mlirModule: MlirModule,
    moduleName: String
  )(
    using Arena,
    Context
  ): Seq[Port]
end FirtoolApi
