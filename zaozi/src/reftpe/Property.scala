// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.reftpe

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.valuetpe.*
import me.jiuyang.zaozi.magic.macros.{referableApplyDynamic, referableApplyDynamicNamed, referableSelectDynamic}
import org.llvm.circt.scalalib.dialect.firrtl.operation.Module as CirctModule
import org.llvm.mlir.scalalib.capi.ir.{Block, Context, Operation, Type, Value}

import java.lang.foreign.Arena

trait Property extends HasOperation:
  private[zaozi] val op: HasOperation
  def operation(
    using TypeImpl
  ): Operation = this.operationImpl
