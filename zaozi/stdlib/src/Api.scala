// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.stdlib

import me.jiuyang.decoder.*
import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.mlir.scalalib.capi.ir.Block
import org.llvm.mlir.scalalib.capi.ir.Context

import java.lang.foreign.Arena

trait BitSetApi[B <: BitSet]:
  extension (bs: B)
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
    ): Node[Bool]
