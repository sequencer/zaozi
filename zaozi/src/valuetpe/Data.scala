// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.valuetpe

import me.jiuyang.zaozi.TypeImpl
import me.jiuyang.zaozi.magic.{DynamicSubfield, UntypedDynamicSubfield}

import org.llvm.mlir.scalalib.capi.ir.{Context, Type}

import java.lang.foreign.Arena

trait Data:
  def toMlirType(
    using Arena,
    Context,
    TypeImpl
  ): Type

trait Width:
  val _width: Int

trait Aggregate extends Data:
  this: DynamicSubfield | UntypedDynamicSubfield =>
  private[zaozi] var instantiating = true
  private[zaozi] val _elements     = collection.mutable.Buffer.empty[BundleField[?]]
