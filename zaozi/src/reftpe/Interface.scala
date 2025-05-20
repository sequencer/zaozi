// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.reftpe

import me.jiuyang.zaozi.valuetpe.*
import me.jiuyang.zaozi.{DVInterface, HWInterface, Parameter, TypeImpl}
import org.llvm.mlir.scalalib.{Operation, Value}

import java.lang.foreign.Arena

trait Interface[T <: HWInterface[?] | DVInterface[?, ?]] extends Referable[T] with HasOperation:
  private[zaozi] val _tpe:       T
  private[zaozi] val _operation: Operation
  def operation(
    using TypeImpl
  ): Operation = this.operationImpl
  def refer(
    using Arena,
    TypeImpl
  ): Value = this.referImpl
