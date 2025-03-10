// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package rvcover.default

import org.llvm.circt.scalalib.smt.capi.{given_TypeApi, TypeApi}
import org.llvm.circt.scalalib.smt.operation.{*, given}
import org.llvm.mlir.scalalib.{Block, Context, Location, LocationApi, Type, Value, given}
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

  def declareFun(
    namePrefix: String,
    tpe:        Type
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Value =
    val op = summon[DeclareFunApi].op(namePrefix, locate, tpe)
    op.operation.appendToBlock()
    op.result

  def smtInt(
    name: String
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Value =
    val op = summon[DeclareFunApi].op(name, locate, summon[TypeApi].getInt())
    op.operation.appendToBlock()
    op.result

  extension (lhs: Value)
    def >(
      rhs: Value | Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Value =
      rhs match
        case rhs: Value => smtIntCmp(lhs, rhs, "gt")
        case rhs: Int   => smtIntCmp(lhs, getInt(rhs), "gt")
    def >=(
      rhs: Value | Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Value =
      rhs match
        case rhs: Value => smtIntCmp(lhs, rhs, "ge")
        case rhs: Int   => smtIntCmp(lhs, getInt(rhs), "ge")
    def <(
      rhs: Value | Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Value =
      rhs match
        case rhs: Value => smtIntCmp(lhs, rhs, "lt")
        case rhs: Int   => smtIntCmp(lhs, getInt(rhs), "lt")
    def <=(
      rhs: Value | Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Value =
      rhs match
        case rhs: Value => smtIntCmp(lhs, rhs, "le")
        case rhs: Int   => smtIntCmp(lhs, getInt(rhs), "le")
    def &(
      rhs: Value
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Value =
      smtAnd(Seq(lhs, rhs))
    def +(
      rhs: Value
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Value =
      smtIntAdd(Seq(lhs, rhs))
    def ===(
      rhs: Value
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Value =
      smtEq(Seq(lhs, rhs))

  def smtIntCmp(
    lhs:  Value,
    rhs:  Value,
    pred: String
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Value =
    val op = summon[IntCmpApi].op(lhs, rhs, pred, locate)
    op.operation.appendToBlock()
    op.result

  def smtAnd(
    values: Seq[Value]
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Value =
    val op = summon[AndApi].op(values, locate)
    op.operation.appendToBlock()
    op.result

  def smtAssert(
    value: Value
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Value =
    val op = summon[AssertApi].op(value, locate)
    op.operation.appendToBlock()
    op.result

  def smtDistinct(
    values: Seq[Value]
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Value =
    val op = summon[DistinctApi].op(values, locate)
    op.operation.appendToBlock()
    op.result

  def smtIntAdd(
    values: Seq[Value]
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Value =
    val op = summon[IntAddApi].op(values, locate)
    op.operation.appendToBlock()
    op.result

  def smtEq(
    values: Seq[Value]
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Value =
    val op = summon[EqApi].op(values, locate)
    op.operation.appendToBlock()
    op.result

  def solver(
    body: (Arena, Context, Block) ?=> Unit
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Unit =
    val op = summon[SolverApi].op(locate)
    body(
      using summon[Arena],
      summon[Context],
      op.bodyBlock
    )
    op.operation.appendToBlock()

  def check(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Unit =
    val op = summon[CheckApi].op(locate)
    smtYield(Seq.empty)(
      using summon[Arena],
      summon[Context],
      op.satBlock
    )
    smtYield(Seq.empty)(
      using summon[Arena],
      summon[Context],
      op.unknownBlock
    )
    smtYield(Seq.empty)(
      using summon[Arena],
      summon[Context],
      op.unsatBlock
    )
    op.operation.appendToBlock()

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
