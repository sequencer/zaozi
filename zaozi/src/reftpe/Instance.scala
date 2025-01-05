// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.reftpe

import me.jiuyang.zaozi.TypeImpl
import me.jiuyang.zaozi.valuetpe.Data
import org.llvm.mlir.scalalib.Operation

trait Instance[T <: Data] extends HasOperation:
  private[zaozi] val _tpe:       T
  private[zaozi] val _operation: Operation
  private[zaozi] val _wire:      Wire[T]

  def operation(
    using TypeImpl
  ): Operation = this.operationImpl

  def io(
    using TypeImpl
  ): Wire[T] = this.ioImpl[T]
