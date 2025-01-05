// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.valuetpe

import me.jiuyang.zaozi.TypeImpl
import org.llvm.mlir.scalalib.{Context, Type}

import java.lang.foreign.Arena

trait Bits extends Data:
  private[zaozi] val _width: Int

  def toMlirType(
    using Arena,
    Context,
    TypeImpl
  ): Type = this.toMlirTypeImpl
