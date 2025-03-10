// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.reftpe

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.valuetpe.*
import me.jiuyang.zaozi.magic.referableSelectDynamic
import org.llvm.circt.scalalib.firrtl.operation.Module as CirctModule
import org.llvm.mlir.scalalib.{Block, Context, Operation, Type, Value}

import java.lang.foreign.Arena
import scala.language.dynamics

trait Referable[T <: Data] extends Dynamic:
  private[zaozi] val _tpe: T
  def refer(
    using Arena,
    TypeImpl
  ): Value

  /** macro to call [[DynamicSubfield.getRefViaFieldValName]] */
  transparent inline def selectDynamic(name: String): Any = ${ referableSelectDynamic('this, 'name) }

trait HasOperation:
  def operation(
    using TypeImpl
  ): Operation
