// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi

import me.jiuyang.zaozi.circtlib.MlirValue
import me.jiuyang.zaozi.internal.NameKind.Droppable
import me.jiuyang.zaozi.internal.{Context, firrtl}

object SInt:
  def apply(width: Width): SInt = new SInt(width)
class SInt(val width: Width) extends Data:
  def firrtlType = new firrtl.SInt(width.toInt, false)

trait AsSInt[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asSInt(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[SInt]

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

// Type Class Implementations
given ToConstSInt[BigInt] with
  extension (ref: BigInt)
    def S(
      width:     Width
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Const[SInt] =
      val tpe     = SInt(width)
      val mlirTpe = tpe.firrtlType.toMLIR(ctx.handler)
      val const   = ctx.handler
        .OpBuilder("firrtl.constant", ctx.currentBlock, SourceLocator(file, line).toMLIR)
        .withNamedAttr(
          "value",
          ctx.handler.firrtlAttrGetIntegerFromString(
            mlirTpe,
            if (width.unknown) math.max(ref.bitLength, 1) else width.get,
            ref.toString,
            10
          )
        )
        // TODO: circt should support type infer for firrtl.constant
        .withResult(mlirTpe)
        .build()
        .results
        .head
      new Const(const, SInt(width))

given ToConstSInt[Int] with
  extension (ref: Int)
    def S(
      width:     Width
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Const[SInt] = BigInt(ref).S(width)

given [R <: Referable[SInt]]: AsBits[SInt, R] with
  extension (ref: R)
    override def asBits(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bits] =
      val mlirValue: MlirValue = ctx.handler
        .OpBuilder(s"firrtl.asUInt", ctx.currentBlock, SourceLocator(file, line).toMLIR)
        .withOperands(Seq(ref.refer))
        .withResultInference(1)
        .build()
        .results
        .head
      new Node[Bits](
        s"${valName.value}_asBits",
        Droppable,
        // todo: from MLIR.
        Bits(ref.tpe.width),
        mlirValue
      )

given [R <: Referable[SInt]]: Add[SInt, SInt, R] with
  extension (ref: R)
    def +(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[SInt] =
      new Node[SInt](
        s"${valName.value}_add",
        Droppable,
        // todo: from MLIR.
        SInt((math.max(ref.tpe.firrtlType.width.get.toInt, that.tpe.firrtlType.width.get.toInt) + 1).W),
        ctx.handler
          .OpBuilder(s"firrtl.add", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[SInt]]: Sub[SInt, SInt, R] with
  extension (ref: R)
    def -(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[SInt] =
      new Node[SInt](
        s"${valName.value}_sub",
        Droppable,
        // todo: from MLIR.
        SInt((math.max(ref.tpe.firrtlType.width.get.toInt, that.tpe.firrtlType.width.get.toInt) + 1).W),
        ctx.handler
          .OpBuilder(s"firrtl.sub", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[SInt]]: Mul[SInt, SInt, R] with
  extension (ref: R)
    def *(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[SInt] =
      new Node[SInt](
        s"${valName.value}_mul",
        Droppable,
        // todo: from MLIR.
        SInt((ref.tpe.firrtlType.width.get.toInt + that.tpe.firrtlType.width.get.toInt).W),
        ctx.handler
          .OpBuilder(s"firrtl.mul", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[SInt]]: Div[SInt, SInt, R] with
  extension (ref: R)
    def /(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[SInt] =
      new Node[SInt](
        "div",
        Droppable,
        // todo: from MLIR.
        ref.tpe,
        ctx.handler
          .OpBuilder(s"firrtl.div", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[SInt]]: Rem[SInt, SInt, R] with
  extension (ref: R)
    def %(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[SInt] =
      new Node[SInt](
        s"${valName.value}_rem",
        Droppable,
        // todo: from MLIR.
        SInt(math.min(ref.tpe.firrtlType.width.get.toInt, that.tpe.firrtlType.width.get.toInt).W),
        ctx.handler
          .OpBuilder(s"firrtl.rem", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[SInt]]: Lt[SInt, Bool, R] with
  extension (ref: R)
    def <(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool] =
      new Node[Bool](
        s"${valName.value}_lt",
        Droppable,
        // todo: from MLIR.
        Bool(),
        ctx.handler
          .OpBuilder(s"firrtl.lt", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[SInt]]: Leq[SInt, Bool, R] with
  extension (ref: R)
    def <=(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool] =
      new Node[Bool](
        s"${valName.value}_leq",
        Droppable,
        // todo: from MLIR.
        Bool(),
        ctx.handler
          .OpBuilder(s"firrtl.leq", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[SInt]]: Gt[SInt, Bool, R] with
  extension (ref: R)
    def >(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool] =
      new Node[Bool](
        s"${valName.value}_gt",
        Droppable,
        // todo: from MLIR.
        Bool(),
        ctx.handler
          .OpBuilder(s"firrtl.gt", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[SInt]]: Geq[SInt, Bool, R] with
  extension (ref: R)
    def >=(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool] =
      new Node[Bool](
        s"${valName.value}_geq",
        Droppable,
        // todo: from MLIR.
        Bool(),
        ctx.handler
          .OpBuilder(s"firrtl.geq", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[SInt]]: Eq[SInt, Bool, R] with
  extension (ref: R)
    def ===(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool] =
      new Node[Bool](
        s"${valName.value}_eq",
        Droppable,
        // todo: from MLIR.
        Bool(),
        ctx.handler
          .OpBuilder(s"firrtl.eq", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[SInt]]: Neq[SInt, Bool, R] with
  extension (ref: R)
    def =/=(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool] =
      new Node[Bool](
        s"${valName.value}_neq",
        Droppable,
        // todo: from MLIR.
        Bool(),
        ctx.handler
          .OpBuilder(s"firrtl.neq", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[SInt], THAT <: Int | Referable[UInt]]: Shl[SInt, THAT, SInt, R] with
  extension (ref: R)
    def <<(
      that:      THAT
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[SInt] =
      that match
        case that: Int             =>
          new Node[SInt](
            s"${valName.value}_shl",
            Droppable,
            // todo: from MLIR.
            SInt((ref.tpe.width.toInt + that).W),
            ctx.handler
              .OpBuilder(s"firrtl.shl", ctx.currentBlock, SourceLocator(file, line).toMLIR)
              .withOperands(Seq(ref.refer))
              .withNamedAttrs(
                Seq(("amount", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), that.toLong)))
              )
              .withResultInference(1)
              .build()
              .results
              .head
          )
        case that: Referable[UInt] =>
          new Node[SInt](
            s"${valName.value}_dshl",
            Droppable,
            // todo: from MLIR.
            SInt((ref.tpe.firrtlType.width.get.toInt + 2 << that.tpe.firrtlType.width.get.toInt - 1).W),
            ctx.handler
              .OpBuilder(s"firrtl.dshl", ctx.currentBlock, SourceLocator(file, line).toMLIR)
              .withOperands(Seq(ref.refer, that.refer))
              .withResultInference(1)
              .build()
              .results
              .head
          )

given [R <: Referable[SInt], THAT <: Int | Referable[UInt]]: Shr[SInt, THAT, SInt, R] with
  extension (ref: R)
    def >>(
      that:      THAT
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[SInt] =
      that match
        case that: Int             =>
          new Node[SInt](
            s"${valName.value}_shr",
            Droppable,
            // todo: from MLIR.
            SInt(math.max(ref.tpe.width.toInt - that, 0).W),
            ctx.handler
              .OpBuilder(s"firrtl.shr", ctx.currentBlock, SourceLocator(file, line).toMLIR)
              .withOperands(Seq(ref.refer))
              .withNamedAttrs(
                Seq(("amount", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), that.toLong)))
              )
              .withResultInference(1)
              .build()
              .results
              .head
          )
        case that: Referable[UInt] =>
          new Node[SInt](
            s"${valName.value}_dshr",
            Droppable,
            // todo: from MLIR.
            ref.tpe,
            ctx.handler
              .OpBuilder(s"firrtl.dshr", ctx.currentBlock, SourceLocator(file, line).toMLIR)
              .withOperands(Seq(ref.refer, that.refer))
              .withResultInference(1)
              .build()
              .results
              .head
          )
