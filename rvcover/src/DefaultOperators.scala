// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package rvcover.default

import org.llvm.circt.scalalib.smt.operation.{*, given}
import org.llvm.mlir.scalalib.{Block, Context, Location, LocationApi, Value, given}
import rvcover.ConstructorApi

import java.lang.foreign.Arena

// When Import the default, all method in ConstructorApi should be exported
val constructorApi = summon[ConstructorApi]
export constructorApi.*

given ConstructorApi with
  def getInt(
    value: Int
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Value =
    val op = summon[IntConstantApi].op(value, locate)
    op.operation.appendToBlock()
    op.result

  def func(
    body: (Arena, Context, Block) ?=> Unit
  )(
    using Arena,
    Context,
    Block
  ): Unit =
    val unknownLocation = summon[LocationApi].locationUnknownGet
    body
    ()

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
  ): Value =
    val op = summon[CheckApi].op(locate, 32.integerTypeGet)
    sat(
      using summon[Arena],
      summon[Context],
      op.satBlock
    )
    unknown(
      using summon[Arena],
      summon[Context],
      op.unknownBlock
    )
    unsat(
      using summon[Arena],
      summon[Context],
      op.unsatBlock
    )
    op.operation.appendToBlock()
    op.result

  def smtYield(
    values: Seq[Value]
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Value =
    val op = summon[YieldApi].op(values, locate)
    op.operation.appendToBlock()
    op.result
end given

private inline def locate(
  using Arena,
  Context,
  sourcecode.File,
  sourcecode.Line
): Location =
  summon[LocationApi].locationFileLineColGet(
    summon[sourcecode.File].value,
    summon[sourcecode.Line].value,
    0
  )
