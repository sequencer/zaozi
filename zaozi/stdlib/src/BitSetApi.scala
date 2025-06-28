// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.stdlib

import me.jiuyang.decoder.*
import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import me.jiuyang.zaozi.default.{*, given}
import org.llvm.mlir.scalalib.capi.ir.Block
import org.llvm.mlir.scalalib.capi.ir.Context

import java.lang.foreign.Arena

given [B <: BitSet]: BitSetApi[B] with
  extension (bs: B)
    // TODO: use QMC for minimization
    def cover(
      signal: Referable[Bits]
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bool] =
      bs.terms.map(bp => bp.value.B === (signal & bp.mask.B)).reduce(_ | _)
