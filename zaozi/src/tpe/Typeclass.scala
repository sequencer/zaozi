// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.internal.Context

trait MonoConnect[D <: Data, SRC <: Referable[D], SINK <: Referable[D]]:
  extension (ref: SINK)
    def :=(
      that:      SRC
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Unit
trait BiConnect[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def <>(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Unit

// primop_1expr_keyword =
//    "asUInt" | "asSInt" | "asClock" | "asAsyncReset" | "cvt"
//  | "neg"    | "not"
//  | "andr"   | "orr"    | "xorr" ;
trait AsBits[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asBits(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bits]
trait AsUInt[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asUInt(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[UInt]
trait AsSInt[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asSInt(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[SInt]
trait AsClock[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asClock(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Clock]
trait AsAsyncReset[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asAsyncReset(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[AsyncReset]
trait Cvt[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def zext(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[SInt]
trait Neg[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def unary_!(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait Not[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def unary_~(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait AndR[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def andR(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool]
trait OrR[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def orR(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool]
trait XorR[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def xorR(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
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
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait Sub[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def -(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait Mul[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def *(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait Div[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def /(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait Rem[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def %(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait Lt[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def <(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool]
trait Leq[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def <=(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool]
trait Gt[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def >(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool]
trait Geq[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def >=(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool]
trait Eq[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def ===(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool]
trait Neq[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def =/=(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool]

trait Dshl[UINT <: Data, D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def <<<(
      that:      Referable[UINT]
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait Dshr[UINT <: Data, D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def >>>(
      that:      Referable[UINT]
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait And[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def &(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait Or[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def |(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait Xor[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def ^(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait Cat[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def ##(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]

//  primop_1expr1int_keyword =
//    "pad" | "shl" | "shr" | "head" | "tail" ;
trait Shl[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def <<(
      that:      Int
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait Shr[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def >>(
      that:      Int
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait Head[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def head(
      that:      Int
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait Tail[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def tail(
      that:      Int
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]
trait Pad[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def pad(
      that:      Int
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]

// primop_1expr2int_keyword = "bits" ;
trait BitsExtract[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def extract(
      hi:        Int,
      lo:        Int
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[D]

trait ToConstUInt[T]:
  extension (ref: T)
    def U(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Const[UInt] = U(-1.W)
    def U(
      width:     Width
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Const[UInt]

trait ToConstSInt[T]:
  extension (ref: T)
    def S(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Const[SInt] = S(-1.W)
    def S(
      width:     Width
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Const[SInt]

trait ToConstBool[T]:
  extension (ref: T)
    def B(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Const[Bool]

trait Mux[Cond <: Data, CondR <: Referable[Cond]]:
  extension (ref: CondR)
    def ?[Ret <: Data](
      con:       Referable[Ret],
      alt:       Referable[Ret]
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Ret]
