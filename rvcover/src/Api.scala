// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package rvcover

import org.llvm.mlir.scalalib.{Block, Context, Value, given}

import java.lang.foreign.Arena

trait ConstructorApi:
  def getInt(
    value: Int
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Value

  def func(
    body: (Arena, Context, Block) ?=> Unit
  )(
    using Arena,
    Context,
    Block
  ): Unit

  def check(
    sat:     (Arena, Context, Block) ?=> Unit
  )(unknown: (Arena, Context, Block) ?=> Unit
  )(unsat:   (Arena, Context, Block) ?=> Unit
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Value

  def smtYield(
    values: Seq[Value]
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Value

end ConstructorApi
