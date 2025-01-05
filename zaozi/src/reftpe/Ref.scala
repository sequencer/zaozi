// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.reftpe

import me.jiuyang.zaozi.TypeImpl
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.mlir.scalalib.{Operation, Value}

import java.lang.foreign.Arena

trait Ref[T <: Data] extends Referable[T] with HasOperation:
  private[zaozi] val _tpe:       T
  private[zaozi] val _operation: Operation

  def operation(
    using TypeImpl
  ): Operation = this.operationImpl

  def refer(
    using Arena,
    TypeImpl
  ): Value = this.referImpl
