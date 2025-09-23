// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import scala.util.chaining.*
import me.jiuyang.zaozi.magic.macros.summonLayersImpl
import me.jiuyang.zaozi.SVAApi
import me.jiuyang.zaozi.InstanceContext
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

import org.llvm.circt.scalalib.capi.dialect.firrtl.given_TypeApi
import org.llvm.circt.scalalib.dialect.firrtl.operation.When
import org.llvm.circt.scalalib.dialect.firrtl.operation.Module as CirctModule
import org.llvm.circt.scalalib.dialect.firrtl.operation.{
  given_LTLAndIntrinsicApi,
  given_LTLClockIntrinsicApi,
  given_LTLConcatIntrinsicApi,
  given_LTLDelayIntrinsicApi,
  given_LTLEventuallyIntrinsicApi,
  given_LTLGoToRepeatIntrinsicApi,
  given_LTLImplicationIntrinsicApi,
  given_LTLIntersectIntrinsicApi,
  given_LTLNonConsecutiveRepeatIntrinsicApi,
  given_LTLNotIntrinsicApi,
  given_LTLOrIntrinsicApi,
  given_LTLRepeatIntrinsicApi,
  given_LTLUntilIntrinsicApi,
  given_VerifAssertIntrinsicApi,
  given_VerifAssumeIntrinsicApi,
  given_VerifCoverIntrinsicApi,
  given_VerifEnsureIntrinsicApi,
  given_VerifRequireIntrinsicApi,
  LTLAndIntrinsicApi,
  LTLClockIntrinsicApi,
  LTLConcatIntrinsicApi,
  LTLDelayIntrinsicApi,
  LTLEventuallyIntrinsicApi,
  LTLGoToRepeatIntrinsicApi,
  LTLImplicationIntrinsicApi,
  LTLIntersectIntrinsicApi,
  LTLNonConsecutiveRepeatIntrinsicApi,
  LTLNotIntrinsicApi,
  LTLOrIntrinsicApi,
  LTLRepeatIntrinsicApi,
  LTLUntilIntrinsicApi,
  VerifAssertIntrinsicApi,
  VerifAssumeIntrinsicApi,
  VerifCoverIntrinsicApi,
  VerifEnsureIntrinsicApi,
  VerifRequireIntrinsicApi
}
import org.llvm.mlir.scalalib.capi.ir.Block
import org.llvm.mlir.scalalib.capi.ir.Context
import org.llvm.mlir.scalalib.capi.ir.Operation
import org.llvm.mlir.scalalib.capi.ir.Type
import org.llvm.mlir.scalalib.capi.ir.Value
import org.llvm.mlir.scalalib.capi.ir.given_OperationApi

import java.lang.foreign.Arena

export given_SVAApi.{assert, assume, cover}

given SVAApi with
  // extension [R <: Referable[Bool]](ref:         R)
  //   def rose(
  //     using Arena,
  //     Context,
  //     Block,
  //     sourcecode.File,
  //     sourcecode.Line,
  //     sourcecode.Name.Machine,
  //     InstanceContext
  //   ): Node[Bool] = ???
  //   def fell(
  //     using Arena,
  //     Context,
  //     Block,
  //     sourcecode.File,
  //     sourcecode.Line,
  //     sourcecode.Name.Machine,
  //     InstanceContext
  //   ): Node[Bool] = ???
  // extension [R <: Referable[T], T <: Data](ref: R)
  //   def stable(
  //     using Arena,
  //     Context,
  //     Block,
  //     sourcecode.File,
  //     sourcecode.Line,
  //     sourcecode.Name.Machine,
  //     InstanceContext
  //   ): Node[Bool] = ???
  //   def past(
  //     n: Int
  //   )(
  //     using Arena,
  //     Context,
  //     Block,
  //     sourcecode.File,
  //     sourcecode.Line,
  //     sourcecode.Name.Machine,
  //     InstanceContext
  //   ): Node[T] = ???

  extension [T <: Referable[Bool] & HasOperation](ref: T)
    def S(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Sequence =
      new Sequence:
        private[zaozi] val op = ref

  extension (ref: Sequence)
    def ##(
      n:    Int
    )(that: Sequence
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Sequence =
      // ##[n] that
      val op0  = summon[LTLDelayIntrinsicApi].op(that.refer, n, Some(0), 1.getUInt, locate)
      op0.operation.appendToBlock()
      // ref ## ##[n] that -> ref ##[n] that
      val op1  = summon[LTLConcatIntrinsicApi].op(ref.refer, op0.result, 1.getUInt, locate)
      op1.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op1.operation

      bool.S

    def ##(
      min:  Int,
      max:  Option[Int]
    )(that: Sequence
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Sequence =
      // ##[n:m] that
      val op0  = summon[LTLDelayIntrinsicApi].op(that.refer, min, max.map(_ - min), 1.getUInt, locate)
      op0.operation.appendToBlock()
      // ref ## ##[n:m] that -> ref ##[n:m] that
      val op1  = summon[LTLConcatIntrinsicApi].op(ref.refer, op0.result, 1.getUInt, locate)
      op1.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op1.operation

      bool.S

    def *(
      n: Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Sequence =
      val op   = summon[LTLRepeatIntrinsicApi].op(ref.refer, n, Some(0), 1.getUInt, locate)
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation

      bool.S

    def *(
      min: Int,
      max: Option[Int]
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Sequence =
      val op   = summon[LTLRepeatIntrinsicApi].op(ref.refer, min, max.map(_ - min), 1.getUInt, locate)
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation

      bool.S

    def *->(
      min: Int,
      max: Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Sequence =
      require(max > min, s"max ($max) must be greater than min ($min) in goto repeat")
      val op   = summon[LTLGoToRepeatIntrinsicApi].op(
        ref.refer,
        min,
        max - min, // 范围大小
        1.getUInt, // clock
        locate
      )
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation

      bool.S

    def *=(
      min: Int,
      max: Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Sequence =
      require(max > min, s"max ($max) must be greater than min ($min) in non-consecutive repeat")
      val op   = summon[LTLNonConsecutiveRepeatIntrinsicApi].op(
        ref.refer,
        min,
        max - min,
        1.getUInt,
        locate
      )
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation

      bool.S

    def ##+(
      that: Sequence
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Sequence = ref.##(1, None)(that)

    def ##*(
      that: Sequence
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Sequence = ref.##(0, None)(that)

    def and(
      that: Sequence
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Sequence =
      val op   = summon[LTLAndIntrinsicApi].op(ref.refer, that.refer, 1.getUInt, locate)
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation

      bool.S

    def intersect(
      that: Sequence
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Sequence =
      val op   = summon[LTLIntersectIntrinsicApi].op(ref.refer, that.refer, 1.getUInt, locate)
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation

      bool.S

    def or(
      that: Sequence
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Sequence =
      val op   = summon[LTLOrIntrinsicApi].op(ref.refer, that.refer, 1.getUInt, locate)
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation

      bool.S

    def not(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Sequence =
      val op   = summon[LTLNotIntrinsicApi].op(ref.refer, 1.getUInt, locate)
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation

      bool.S

  extension [T <: Referable[Bool] & HasOperation](ref: T)
    def throughout(
      that: Sequence
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Sequence =
      // %repexpr = ltl.repeat %expr, 0 : !ltl.sequence
      // %res = ltl.intersect %repexpr, %s : !ltl.sequence
      val repexpr = summon[LTLRepeatIntrinsicApi].op(ref.refer, 0, None, 1.getUInt, locate)
      repexpr.operation.appendToBlock()
      val res     = summon[LTLIntersectIntrinsicApi].op(repexpr.result, that.refer, 1.getUInt, locate)
      res.operation.appendToBlock()
      val bool    = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = res.operation

      bool.S
  extension (ref:                                      Sequence)
    def within(
      that: Sequence
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Sequence =
      // within: ref occurs within the duration of 'that'
      // true ##[*] s1 ##[*] true intersect s2
      true.B.S.##*(ref).##*(true.B.S).intersect(that)

  // Property Layer
  extension (ref: Sequence)
    def P(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Property =
      new Property:
        private[zaozi] val op = ref.op

    def |->(
      that: Property
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Property =
      // ref |-> that: implication property (strong implication)
      val op   = summon[LTLImplicationIntrinsicApi].op(ref.refer, that.refer, 1.getUInt, locate)
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation

      bool.S.P

    def |=>(
      that: Property
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Property =
      // ref |=> that: implication property (weak implication)
      // ref ##1 true |-> that
      ref.##(1)(true.B.S) |-> that

  extension (ref: Property)
    def implies(
      that: Property
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Property =
      // Logical implication: ref => that is equivalent to !ref | that
      val op0  = summon[LTLNotIntrinsicApi].op(ref.refer, 1.getUInt, locate)
      op0.operation.appendToBlock()
      val op1  = summon[LTLOrIntrinsicApi].op(op0.result, that.refer, 1.getUInt, locate)
      op1.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op1.operation

      bool.S.P

    def iff(
      that: Property
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Property =
      // Logical equivalence: ref <=> that is !(ref | that) | (ref & that)

      // !(ref | that)
      val or    = summon[LTLOrIntrinsicApi].op(ref.refer, that.refer, 1.getUInt, locate)
      or.operation.appendToBlock()
      val left  = summon[LTLNotIntrinsicApi].op(or.result, 1.getUInt, locate)
      left.operation.appendToBlock()
      // ref & that
      val right = summon[LTLAndIntrinsicApi].op(ref.refer, that.refer, 1.getUInt, locate)
      right.operation.appendToBlock()
      val op    = summon[LTLOrIntrinsicApi].op(left.result, right.result, 1.getUInt, locate)
      op.operation.appendToBlock()
      val bool  = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation

      bool.S.P
  extension (ref: Sequence)
    def #-#(
      that: Property
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Property =
      // ref #-# that: strong implication property (sequence implication)
      // Equivalent to: !(ref -> !that)

      // %np = ltl.not %p : !ltl.property
      // %impl = ltl.implication %s, %np : !ltl.property
      // %res = ltl.not %impl : !ltl.property

      val np   = summon[LTLNotIntrinsicApi].op(that.refer, 1.getUInt, locate)
      np.operation.appendToBlock()
      val impl = summon[LTLImplicationIntrinsicApi].op(ref.refer, np.result, 1.getUInt, locate)
      impl.operation.appendToBlock()
      val res  = summon[LTLNotIntrinsicApi].op(impl.result, 1.getUInt, locate)
      res.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = res.operation

      bool.S.P

    def #=#(
      that: Property
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Property =
      // ref #=# that: sequence equivalence property
      // Equivalent to: (ref #-# that) & (that #-# ref)
      // Equivalent to: (ref #-# that) & !(that -> !ref)

      val left = ref #-# that

      val nref  = summon[LTLNotIntrinsicApi].op(ref.refer, 1.getUInt, locate)
      nref.operation.appendToBlock()
      val impl  = summon[LTLImplicationIntrinsicApi].op(that.refer, nref.result, 1.getUInt, locate)
      impl.operation.appendToBlock()
      val right = summon[LTLNotIntrinsicApi].op(impl.result, 1.getUInt, locate)
      right.operation.appendToBlock()

      val op   = summon[LTLAndIntrinsicApi].op(left.refer, right.result, 1.getUInt, locate)
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation

      bool.S.P

  extension (ref: Property)
    def nextTime(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Property =
      // nextTime: equivalent to ltl.delay property by 1 cycle
      val op   = summon[LTLDelayIntrinsicApi].op(ref.refer, 1, Some(0), 1.getUInt, locate)
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation
      bool.S.P

    def nextTime(
      n: Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Property =
      // nextTime: equivalent to ltl.delay property by n cycle
      val op   = summon[LTLDelayIntrinsicApi].op(ref.refer, n, Some(0), 1.getUInt, locate)
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation
      bool.S.P

    def always(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Property =
      // always: equivalent to ltl.repeat with 0
      val op   = summon[LTLRepeatIntrinsicApi].op(ref.refer, 0, None, 1.getUInt, locate)
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation
      bool.S.P

    def always(
      min: Int,
      max: Int
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Property =
      // always: equivalent to ltl.repeat with min and max
      val op   = summon[LTLRepeatIntrinsicApi].op(ref.refer, min, Some(max - min), 1.getUInt, locate)
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation
      bool.S.P

    def eventually(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Property =
      val op   = summon[LTLEventuallyIntrinsicApi].op(ref.refer, 1.getUInt, locate)
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation
      bool.S.P

    def until(
      that: Property
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Property =
      // until: equivalent to ltl.until
      val op   = summon[LTLUntilIntrinsicApi].op(ref.refer, that.refer, 1.getUInt, locate)
      op.operation.appendToBlock()
      val bool = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation
      bool.S.P

    def untilWith(
      that: Property
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Property =
      // untilWith: equivalent to ltl.until with inclusive semantics
      // This is typically modeled as: (ref until that) implies (ref and that)
      val left  = ref.until(that)
      val op    = summon[LTLAndIntrinsicApi].op(ref.refer, that.refer, 1.getUInt, locate)
      op.operation.appendToBlock()
      val right = new Ref[Bool]:
        private[zaozi] val _tpe       = new Object with Bool
        private[zaozi] val _operation = op.operation

      left.implies(right.S.P)

  def assert(
    property: Property,
    clock:    Option[Referable[Clock]] = None,
    label:    Option[String] = None
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name.Machine,
    InstanceContext
  ): Unit =
    summon[VerifAssertIntrinsicApi]
      .op(property.refer, clock.getOrElse(true.B).refer, label.getOrElse(summon[sourcecode.Name].value), locate)
      .operation
      .appendToBlock()

  def assume(
    property: Property,
    clock:    Option[Referable[Clock]] = None,
    label:    Option[String] = None
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name.Machine,
    InstanceContext
  ): Unit =
    summon[VerifAssumeIntrinsicApi]
      .op(property.refer, clock.getOrElse(true.B).refer, label.getOrElse(summon[sourcecode.Name].value), locate)
      .operation
      .appendToBlock()

  def cover(
    property: Property,
    clock:    Option[Referable[Clock]] = None,
    label:    Option[String] = None
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name.Machine,
    InstanceContext
  ): Unit =
    summon[VerifCoverIntrinsicApi]
      .op(property.refer, clock.getOrElse(true.B).refer, label.getOrElse(summon[sourcecode.Name].value), locate)
      .operation
      .appendToBlock()

end given
