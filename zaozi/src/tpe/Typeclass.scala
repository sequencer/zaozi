// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.internal.Context

trait MonoConnect[D <: Data, SRC <: Referable[D], SINK <: Referable[D]]:
  extension (ref: SINK)
    def :=(
      that:      SRC
    )(
      using ctx: Context
    ): Unit
trait BiConnect[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def <>(
      that:      R
    )(
      using ctx: Context
    ): Unit

// primop_1expr_keyword =
//    "asUInt" | "asSInt" | "asClock" | "asAsyncReset" | "cvt"
//  | "neg"    | "not"
//  | "andr"   | "orr"    | "xorr" ;
trait AsUInt[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asUInt(
      using ctx: Context
    ): Node[UInt]
trait AsSInt[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asSInt(
      using ctx: Context
    ): Node[SInt]
trait AsClock[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asClock(
      using ctx: Context
    ): Node[Clock]
trait AsAsyncReset[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asAsyncReset(
      using ctx: Context
    ): Node[AsyncReset]
trait Cvt[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def zext(
      using ctx: Context
    ): Node[SInt]
trait Neg[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def unary_!(
      using ctx: Context
    ): Node[D]
trait Not[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def unary_~(
      using ctx: Context
    ): Node[D]
trait AndR[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def andR(
      using ctx: Context
    ): Node[Bool]
trait OrR[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def orR(
      using ctx: Context
    ): Node[Bool]
trait XorR[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def xorR(
      using ctx: Context
    ): Node[D]

//  primop_2expr_keyword =
//    "add" | "sub" | "mul" | "div" | "mod"
//      | "lt" | "leq" | "gt" | "geq" | "eq" | "neq"
//      | "dshl" | "dshr"
//      | "and" | "or" | "xor" | "cat";
trait Add[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def +(
      that:      R
    )(
      using ctx: Context
    ): Node[D]
trait Sub[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def -(
      that:      R
    )(
      using ctx: Context
    ): Node[D]
trait Mul[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def *(
      that:      R
    )(
      using ctx: Context
    ): Node[D]
trait Div[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def /(
      that:      R
    )(
      using ctx: Context
    ): Node[D]
trait Rem[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def %(
      that:      R
    )(
      using ctx: Context
    ): Node[D]
trait Lt[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def <(
      that:      R
    )(
      using ctx: Context
    ): Node[Bool]
trait Leq[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def <=(
      that:      R
    )(
      using ctx: Context
    ): Node[Bool]
trait Gt[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def >(
      that:      R
    )(
      using ctx: Context
    ): Node[Bool]
trait Geq[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def >=(
      that:      R
    )(
      using ctx: Context
    ): Node[Bool]
trait Eq[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def ===(
      that:      R
    )(
      using ctx: Context
    ): Node[Bool]
trait Neq[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def !==(
      that:      R
    )(
      using ctx: Context
    ): Node[Bool]
    def =/=(
      that:      R
    )(
      using ctx: Context
    ): Node[Bool] = ref !== that

trait Dshl[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def <<<(
      that:      Referable[UInt]
    )(
      using ctx: Context
    ): Node[D]
trait Dshr[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def >>>(
      that:      Referable[UInt]
    )(
      using ctx: Context
    ): Node[D]
trait And[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def &(
      that:      R
    )(
      using ctx: Context
    ): Node[D]
trait Or[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def |(
      that:      R
    )(
      using ctx: Context
    ): Node[D]
trait Xor[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def ^(
      that:      R
    )(
      using ctx: Context
    ): Node[D]
trait Cat[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def ##(
      that:      R
    )(
      using ctx: Context
    ): Node[D]

//  primop_1expr1int_keyword =
//    "pad" | "shl" | "shr" | "head" | "tail" ;
trait Shl[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def <<(
      that:      Int
    )(
      using ctx: Context
    ): Node[D]
trait Shr[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def >>(
      that:      Int
    )(
      using ctx: Context
    ): Node[D]
trait Head[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def head(
      that:      Int
    )(
      using ctx: Context
    ): Node[D]
trait Tail[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def tail(
      that:      Int
    )(
      using ctx: Context
    ): Node[D]
trait Pad[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def pad(
      that:      Int
    )(
      using ctx: Context
    ): Node[D]

// primop_1expr2int_keyword = "bits" ;
trait Bits[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def extract(
      hi:        Int,
      lo:        Int
    )(
      using ctx: Context
    ): Node[UInt]

/** TODO: should have a trans def or dynamic method to summon element is D
  * {{{
  *   class B extends Bundle {
  *     val b = Aligned(Bool())
  *   }
  *   class A extends Bundle {
  *     val a = Flipped(new Bundle {
  *       val b = Aligned(Bool())
  *       val c = Aligned(new B)
  *     })
  *   }
  *   val reg: Reg[A]
  *   reg.a : Reg[Bundle]
  *   reg.a.b : Reg[Bool]
  *   reg.a.c : Reg[B]
  * }}}
  */
trait Subaccess[D <: Bundle, R <: Referable[D]]:
  extension (ref: R)
    def field(
      that:      String
    )(
      using ctx: Context
    ): Ref[Data]
trait Subindex[E <: Data, D <: Vec[E], R <: Referable[D]]:
  extension (ref: R)
    def field(
      that:      Int
    )(
      using ctx: Context
    ): Ref[E]

trait ToConstUInt[T]:
  extension (ref: T)
    def U(
      using ctx: Context
    ): Const[UInt] = U(-1.W)
    def U(
      width:     Width
    )(
      using ctx: Context
    ): Const[UInt]

trait ToConstSInt[T]:
  extension (ref: T)
    def S(
      using ctx: Context
    ): Const[SInt] = S(-1.W)
    def S(
      width:     Width
    )(
      using ctx: Context
    ): Const[SInt]

trait ToConstBool[T]:
  extension (ref: T)
    def B(
      using ctx: Context
    ): Const[Bool]
