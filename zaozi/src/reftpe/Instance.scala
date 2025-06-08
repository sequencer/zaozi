// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.reftpe

import me.jiuyang.zaozi.TypeImpl
import me.jiuyang.zaozi.valuetpe.Data
import org.llvm.mlir.scalalib.capi.ir.Operation
import me.jiuyang.zaozi.HWInterface
import me.jiuyang.zaozi.DVInterface

trait Instance[IOTpe <: HWInterface[?], ProbeTpe <: DVInterface[?, ?]] extends HasOperation:
  private[zaozi] val _ioTpe:     IOTpe
  private[zaozi] val _probeTpe:  ProbeTpe
  private[zaozi] val _operation: Operation
  private[zaozi] val _ioWire:    Wire[IOTpe]
  private[zaozi] val _probeWire: Wire[ProbeTpe]

  def operation(
    using TypeImpl
  ): Operation = this.operationImpl

  def io(
    using TypeImpl
  ): Wire[IOTpe] = this.ioImpl[IOTpe]

  def probe(
    using TypeImpl
  ): Wire[ProbeTpe] = this.probeImpl[ProbeTpe]
