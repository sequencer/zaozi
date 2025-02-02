// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi

import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.circt.scalalib.firrtl.operation.{Module as CirctModule, When}
import org.llvm.mlir.scalalib.{Block, Context, Operation, Type, Value}

import java.lang.foreign.Arena

/** Rebuild the [[Layer]] with each [[Layer]] contains the entire tree. */
trait LayerTree:
  layer =>
  def _name:      String
  def _children:  Seq[LayerTree]
  def _parent:    Option[LayerTree] = None
  def _hierarchy: Seq[LayerTree]    =
    _parent match
      case Some(p) => p._hierarchy :+ this
      case None    => Seq(this)
  def _dfs:       Seq[LayerTree]    =
    this +: _children.flatMap(_._dfs)
  def _rebuild:   LayerTree         =
    def rebuildLayer(oldLayer: LayerTree, parent: Option[LayerTree]): LayerTree =
      new LayerTree:
        override def _name:     String            = oldLayer._name
        override def _children: Seq[LayerTree]    =
          oldLayer._children.map(child => rebuildLayer(child, Some(this)))
        override def _parent:   Option[LayerTree] = parent
    rebuildLayer(this, None)

/** Serializable Layer definition. */
case class Layer(name: String, children: Seq[Layer] = Seq.empty)

trait Parameter:
  def moduleName: String
  def layers:     Seq[Layer]
  def layerTrees(
    using ConstructorApi
  ): Seq[LayerTree] = layers.map(_.toLayerTree)

class HWInterface[P <: Parameter](
  using P)
    extends Bundle
class DVInterface[P <: Parameter](
  using P)
    extends ProbeBundle

trait ConstructorApi:
  def Clock(): Clock

  def Reset(): Reset

  def AsyncReset(): Reset

  def UInt(width: Width): UInt

  def Bits(width: Width): Bits

  def SInt(width: Width): SInt

  def Bool(): Bool

  def Vec[T <: Data](size: Int, tpe: T): Vec[T]

  def when[COND <: Referable[Bool]](
    cond: COND
  )(body: (Arena, Context, Block) ?=> Unit
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): When

  extension (when: When)
    def otherwise(
      body: (Arena, Context, Block) ?=> Unit
    )(
      using Arena,
      Context,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Unit

  extension (layer: Layer) def toLayerTree: LayerTree

  def Module[PARAM <: Parameter, I <: HWInterface[PARAM], P <: DVInterface[PARAM]](
    io:    I,
    probe: P
  )(body:  (Arena, Context, Block, Seq[LayerTree], PARAM, Interface[I], Interface[P]) ?=> Unit
  )(
    using Arena,
    Context,
    PARAM
  ): CirctModule

  def Wire[T <: Data](
    refType: T
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Wire[T]
  def Reg[T <: Data](
    refType: T
  )(
    using Arena,
    Context,
    Block,
    Ref[Clock],
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Reg[T]
  def RegInit[T <: Data](
    input: Const[T]
  )(
    using Arena,
    Context,
    Block,
    Ref[Clock],
    Ref[Reset],
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Reg[T]
  extension (bigInt: BigInt)
    def U(
      width: Width
    )(
      using Arena,
      Context,
      Block
    ):     Const[UInt]
    def U(
      using Arena,
      Context,
      Block
    ):     Const[UInt]
    def B(
      using Arena,
      Context,
      Block
    ):     Const[Bits]
    def S(
      width: Width
    )(
      using Arena,
      Context,
      Block
    ):     Const[SInt]
    def S(
      using Arena,
      Context,
      Block
    ):     Const[SInt]
    def W: Width
  extension (bool:   Boolean)
    def B(
      using Arena,
      Context,
      Block
    ): Const[Bool]
end ConstructorApi

trait AsBits[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asBits(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[Bits]
trait AsBool[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asBool(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[Bool]
trait AsSInt[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asSInt(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[SInt]
trait AsUInt[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asUInt(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[UInt]

trait ProbeDefine[D <: Data & CanProbe, P <: RWProbe[D] | RProbe[D], SRC <: Referable[D], SINK <: Referable[P]]:
  extension (ref: SINK)
    def <==(
      that: SRC
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line
    ): Unit
trait MonoConnect[D <: Data, SRC <: Referable[D], SINK <: Referable[D]]:
  extension (ref: SINK)
    def :=(
      that: SRC
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line
    ): Unit
trait Cvt[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def zext(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Neg[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def unary_!(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Not[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def unary_~(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait AndR[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def andR(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait OrR[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def orR(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait XorR[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def xorR(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Add[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def +(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Sub[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def -(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Mul[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def *(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Div[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def /(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Rem[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def %(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Lt[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def <(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Leq[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def <=(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Gt[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def >(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Geq[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def >=(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Eq[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def ===(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Neq[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def =/=(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait And[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def &(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Or[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def |(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Xor[D <: Data, RET <: Data, R <: Referable[D]]:
  extension (ref: R)
    def ^(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[RET]
trait Cat[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def ##(
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[D]

trait Shl[D <: Data, THAT, OUT <: Data, R <: Referable[D]]:
  extension (ref: R)
    def <<(
      that: THAT
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[OUT]
trait Shr[D <: Data, THAT, OUT <: Data, R <: Referable[D]]:
  extension (ref: R)
    def >>(
      that: THAT
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[D]
trait Head[D <: Data, THAT, OUT <: Data, R <: Referable[D]]:
  extension (ref: R)
    def head(
      that: THAT
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[OUT]
trait Tail[D <: Data, THAT, OUT <: Data, R <: Referable[D]]:
  extension (ref: R)
    def tail(
      that: THAT
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[OUT]
trait Pad[D <: Data, THAT, OUT <: Data, R <: Referable[D]]:
  extension (ref: R)
    def pad(
      that: THAT
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[OUT]
trait ExtractRange[D <: Data, IDX, E <: Data, R <: Referable[D]]:
  extension (ref: R)
    def bits(
      hi: IDX,
      lo: IDX
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[E]
trait ExtractElement[D <: Data, E <: Data, R <: Referable[D], IDX]:
  extension (ref: R)
    def apply(
      idx: IDX
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[E]
trait Mux[Cond <: Data, CondR <: Referable[Cond]]:
  extension (ref: CondR)
    def ?[Ret <: Data](
      con: Referable[Ret],
      alt: Referable[Ret]
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Node[Ret]
trait RefElement[D <: Data, E <: Data, R <: Referable[D], IDX]:
  extension (ref: R)
    def ref(
      idx: IDX
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    ): Ref[E]
trait BitsApi[R <: Referable[Bits]]
    extends AsSInt[Bits, R]
    with AsUInt[Bits, R]
    with Not[Bits, Bits, R]
    with AndR[Bits, Bool, R]
    with OrR[Bits, Bool, R]
    with XorR[Bits, Bool, R]
    with Eq[Bits, Bool, R]
    with Neq[Bits, Bool, R]
    with And[Bits, Bits, R]
    with Or[Bits, Bits, R]
    with Xor[Bits, Bits, R]
    with Cat[Bits, R]
    with Shl[Bits, Int | Referable[UInt], Bits, R]
    with Shr[Bits, Int | Referable[UInt], Bits, R]
    with Head[Bits, Int, Bits, R]
    with Tail[Bits, Int, Bits, R]
    with Pad[Bits, Int, Bits, R]
    with ExtractRange[Bits, Int, Bits, R]

trait BoolApi[R <: Referable[Bool]]
    extends AsBits[Bool, R]
    with Neg[Bool, Bool, R]
    with Eq[Bool, Bool, R]
    with Neq[Bool, Bool, R]
    with And[Bool, Bool, R]
    with Or[Bool, Bool, R]
    with Xor[Bool, Bool, R]
    with Mux[Bool, R]
trait UIntApi[R <: Referable[UInt]]
    extends AsBits[UInt, R]
    with Add[UInt, UInt, R]
    with Sub[UInt, UInt, R]
    with Mul[UInt, UInt, R]
    with Div[UInt, UInt, R]
    with Rem[UInt, UInt, R]
    with Lt[UInt, Bool, R]
    with Leq[UInt, Bool, R]
    with Gt[UInt, Bool, R]
    with Geq[UInt, Bool, R]
    with Eq[UInt, Bool, R]
    with Neq[UInt, Bool, R]
    with Shl[UInt, Int | Referable[UInt], UInt, R]
    with Shr[UInt, Int | Referable[UInt], UInt, R]
trait SIntApi[R <: Referable[SInt]]
    extends AsBits[SInt, R]
    with Add[SInt, SInt, R]
    with Sub[SInt, SInt, R]
    with Mul[SInt, SInt, R]
    with Div[SInt, SInt, R]
    with Rem[SInt, SInt, R]
    with Lt[SInt, Bool, R]
    with Leq[SInt, Bool, R]
    with Gt[SInt, Bool, R]
    with Geq[SInt, Bool, R]
    with Neq[SInt, Bool, R]
    with Shl[SInt, Int | Referable[UInt], SInt, R]
    with Shr[SInt, Int | Referable[UInt], SInt, R]

trait BundleApi[T <: Bundle, R <: Referable[T]]

trait VecApi[E <: Data, V <: Vec[E], R <: Referable[V]] extends ExtractElement[V, E, R, Referable[UInt] | Int]

trait ClockApi[R <: Referable[Clock]]

trait ResetApi[R <: Referable[Reset]]

trait TypeImpl:
  extension (ref: Interface[?])
    private[zaozi] def operationImpl: Operation
    def referImpl(
      using Arena
    ):                                Value
  extension (ref: Wire[?])
    private[zaozi] def operationImpl: Operation
    def referImpl(
      using Arena
    ):                                Value
  extension (ref: Reg[?])
    private[zaozi] def operationImpl: Operation
    def referImpl(
      using Arena
    ):                                Value
  extension (ref: Node[?])
    def operationImpl: Operation
    def referImpl(
      using Arena
    ):                 Value
  extension (ref: Ref[?])
    def operationImpl: Operation
    def referImpl(
      using Arena
    ):                 Value
  extension (ref: Const[?])
    def operationImpl: Operation
    def referImpl(
      using Arena
    ):                 Value
  extension (ref: Instance[?, ?])
    def operationImpl:        Operation
    def ioImpl[T <: Data]:    Wire[T]
    def probeImpl[T <: Data]: Wire[T]

  extension (ref: Reset)
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type
  extension (ref: Clock)
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type
  extension (ref: UInt)
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type
  extension (ref: SInt)
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type
  extension (ref: Bits)
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type
  extension (ref: Analog)
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type
  extension (ref: Bool)
    def toMlirTypeImpl(
      using Arena,
      Context
    ): Type
  extension (ref: ProbeBundle)
    def elements: Seq[BundleField[?]]
    def toMlirTypeImpl(
      using Arena,
      Context
    ):            Type
    def ReadProbeImpl[T <: Data & CanProbe](
      name:  Option[String],
      tpe:   T,
      layer: LayerTree
    )(
      using sourcecode.Name
    ):            BundleField[RProbe[T]]
    def ReadWriteProbeImpl[T <: Data & CanProbe](
      name:  Option[String],
      tpe:   T,
      layer: LayerTree
    )(
      using sourcecode.Name
    ):            BundleField[RWProbe[T]]
  extension (ref: Bundle)
    def elements: Seq[BundleField[?]]
    def toMlirTypeImpl(
      using Arena,
      Context
    ):            Type
    def FlippedImpl[T <: Data](
      name: Option[String],
      tpe:  T
    )(
      using sourcecode.Name
    ):            BundleField[T]
    def AlignedImpl[T <: Data](
      name: Option[String],
      tpe:  T
    )(
      using sourcecode.Name
    ):            BundleField[T]
  extension (ref: RProbe[?])
    def toMlirTypeImpl(
      using Arena,
      Context,
      TypeImpl
    ): Type
  extension (ref: RWProbe[?])
    def toMlirTypeImpl(
      using Arena,
      Context,
      TypeImpl
    ): Type
  extension (ref: Vec[?])
    def elementType: Data
    def count:       Int
    def toMlirTypeImpl(
      using Arena,
      Context
    ):               Type
  extension (ref: ProbeBundle)
    def getRefViaFieldValNameImpl[E <: Data](
      refer:        Value,
      fieldValName: String
    )(
      using Arena,
      Block,
      Context,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    )(
      using TypeImpl
    ): Ref[E]
  extension (ref: Bundle)
    def getRefViaFieldValNameImpl[E <: Data](
      refer:        Value,
      fieldValName: String
    )(
      using Arena,
      Block,
      Context,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name
    )(
      using TypeImpl
    ): Ref[E]
