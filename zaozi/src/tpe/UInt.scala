package me.jiuyang.zaozi

import me.jiuyang.zaozi.circtlib.MlirValue
import me.jiuyang.zaozi.internal.NameKind.Droppable
import me.jiuyang.zaozi.internal.{firrtl, Context}

object UInt:
  def apply(width: Width): UInt = new UInt(width)

class UInt(val width: Width) extends Data:
  def firrtlType = new firrtl.UInt(width.toInt, false)

// Type Class Implementations
given ToConstUInt[BigInt] with
  extension (ref: BigInt)
    def U(
      width:     Width
    )(
      using ctx: Context
    ): Const[UInt] =
      val tpe     = UInt(width)
      val mlirTpe = tpe.firrtlType.toMLIR(ctx.handler)
      val const   = ctx.handler
        .OpBuilder("firrtl.constant", ctx.currentBlock, ctx.handler.unkLoc)
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
      new Const(const, UInt(width))

given ToConstUInt[Int] with
  extension (ref: Int)
    def U(
      width:     Width
    )(
      using ctx: Context
    ): Const[UInt] = BigInt(ref).U(width)

given [R <: Referable[UInt]]: AsUInt[UInt, R] with
  extension (ref: R)
    override def asUInt(
      using ctx: Context
    ): Node[UInt] =
      val mlirValue: MlirValue = ctx.handler
        .OpBuilder(s"firrtl.asUInt", ctx.currentBlock, ctx.handler.unkLoc)
        .withOperands(Seq(ref.refer))
        .withResultInference(1)
        .build()
        .results
        .head
      new Node[UInt](
        "_asUInt",
        Droppable,
        // todo: from MLIR.
        ref.tpe,
        mlirValue
      )

given [R <: Referable[UInt]]: AsSInt[UInt, R] with
  extension (ref: R)
    override def asSInt(
      using ctx: Context
    ): Node[SInt] =
      val mlirValue: MlirValue = ctx.handler
        .OpBuilder(s"firrtl.asUInt", ctx.currentBlock, ctx.handler.unkLoc)
        .withOperands(Seq(ref.refer))
        .withResultInference(1)
        .build()
        .results
        .head
      new Node[SInt](
        "_asSInt",
        Droppable,
        // todo: from MLIR.
        // todo: what if width = -1, 0, 1?
        SInt(ref.tpe.width),
        mlirValue
      )

given [R <: Referable[UInt]]: Cvt[UInt, R] with
  extension (ref: R)
    override def zext(
      using ctx: Context
    ): Node[SInt] =
      val mlirValue: MlirValue = ctx.handler
        .OpBuilder(s"firrtl.cvt", ctx.currentBlock, ctx.handler.unkLoc)
        .withOperands(Seq(ref.refer))
        .withResultInference(1)
        .build()
        .results
        .head
      new Node[SInt](
        "_asSInt",
        Droppable,
        // todo: from MLIR.
        // todo: what if width = -1, 0, 1?
        if (ref.tpe.width.unknown) SInt(-1.W) else SInt((ref.tpe.width.toInt + 1).W),
        mlirValue
      )

given [R <: Referable[UInt]]: Not[UInt, R] with
  extension (ref: R)
    override def unary_~(
      using ctx: Context
    ): Node[UInt] =
      val mlirValue: MlirValue = ctx.handler
        .OpBuilder(s"firrtl.not", ctx.currentBlock, ctx.handler.unkLoc)
        .withOperands(Seq(ref.refer))
        .withResultInference(1)
        .build()
        .results
        .head
      new Node[UInt](
        "_not",
        Droppable,
        ref.tpe,
        mlirValue
      )

given [R <: Referable[UInt]]: AndR[UInt, R] with
  extension (ref: R)
    override def andR(
      using ctx: Context
    ): Node[Bool] =
      val mlirValue: MlirValue = ctx.handler
        .OpBuilder(s"firrtl.andr", ctx.currentBlock, ctx.handler.unkLoc)
        .withOperands(Seq(ref.refer))
        .withResultInference(1)
        .build()
        .results
        .head
      new Node[Bool](
        "_andR",
        Droppable,
        Bool(),
        mlirValue
      )

given [R <: Referable[UInt]]: OrR[UInt, R] with
  extension (ref: R)
    override def orR(
      using ctx: Context
    ): Node[Bool] =
      val mlirValue: MlirValue = ctx.handler
        .OpBuilder(s"firrtl.orr", ctx.currentBlock, ctx.handler.unkLoc)
        .withOperands(Seq(ref.refer))
        .withResultInference(1)
        .build()
        .results
        .head
      new Node[Bool](
        "_orR",
        Droppable,
        Bool(),
        mlirValue
      )

given [R <: Referable[UInt]]: Add[UInt, R] with
  extension (ref: R)
    def +(
      that:      R
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_add",
        Droppable,
        // todo: from MLIR.
        UInt((math.max(ref.tpe.firrtlType.width.get.toInt, that.tpe.firrtlType.width.get.toInt) + 1).W),
        ctx.handler
          .OpBuilder(s"firrtl.add", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Sub[UInt, R] with
  extension (ref: R)
    def -(
      that:      R
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_sub",
        Droppable,
        // todo: from MLIR.
        UInt((math.max(ref.tpe.firrtlType.width.get.toInt, that.tpe.firrtlType.width.get.toInt) + 1).W),
        ctx.handler
          .OpBuilder(s"firrtl.sub", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Mul[UInt, R] with
  extension (ref: R)
    def *(
      that:      R
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_mul",
        Droppable,
        // todo: from MLIR.
        UInt((ref.tpe.firrtlType.width.get.toInt + that.tpe.firrtlType.width.get.toInt).W),
        ctx.handler
          .OpBuilder(s"firrtl.mul", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Div[UInt, R] with
  extension (ref: R)
    def /(
      that:      R
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "div",
        Droppable,
        // todo: from MLIR.
        ref.tpe,
        ctx.handler
          .OpBuilder(s"firrtl.div", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Rem[UInt, R] with
  extension (ref: R)
    def %(
      that:      R
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_rem",
        Droppable,
        // todo: from MLIR.
        UInt(math.min(ref.tpe.firrtlType.width.get.toInt, that.tpe.firrtlType.width.get.toInt).W),
        ctx.handler
          .OpBuilder(s"firrtl.rem", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Lt[UInt, R] with
  extension (ref: R)
    def <(
      that:      R
    )(
      using ctx: Context
    ): Node[Bool] =
      new Node[Bool](
        "_lt",
        Droppable,
        // todo: from MLIR.
        Bool(),
        ctx.handler
          .OpBuilder(s"firrtl.lt", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Leq[UInt, R] with
  extension (ref: R)
    def <=(
      that:      R
    )(
      using ctx: Context
    ): Node[Bool] =
      new Node[Bool](
        "_leq",
        Droppable,
        // todo: from MLIR.
        Bool(),
        ctx.handler
          .OpBuilder(s"firrtl.leq", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Gt[UInt, R] with
  extension (ref: R)
    def >(
      that:      R
    )(
      using ctx: Context
    ): Node[Bool] =
      new Node[Bool](
        "_gt",
        Droppable,
        // todo: from MLIR.
        Bool(),
        ctx.handler
          .OpBuilder(s"firrtl.gt", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Geq[UInt, R] with
  extension (ref: R)
    def >=(
      that:      R
    )(
      using ctx: Context
    ): Node[Bool] =
      new Node[Bool](
        "_geq",
        Droppable,
        // todo: from MLIR.
        Bool(),
        ctx.handler
          .OpBuilder(s"firrtl.geq", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Eq[UInt, R] with
  extension (ref: R)
    def ===(
      that:      R
    )(
      using ctx: Context
    ): Node[Bool] =
      new Node[Bool](
        "_eq",
        Droppable,
        // todo: from MLIR.
        Bool(),
        ctx.handler
          .OpBuilder(s"firrtl.eq", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Neq[UInt, R] with
  extension (ref: R)
    def !==(
      that:      R
    )(
      using ctx: Context
    ): Node[Bool] =
      new Node[Bool](
        "_neq",
        Droppable,
        // todo: from MLIR.
        Bool(),
        ctx.handler
          .OpBuilder(s"firrtl.neq", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Dshl[UInt, R] with
  extension (ref: R)
    def <<<(
      that:      Referable[UInt]
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_dshr",
        Droppable,
        // todo: from MLIR.
        UInt((ref.tpe.firrtlType.width.get.toInt + 2 << that.tpe.firrtlType.width.get.toInt - 1).W),
        ctx.handler
          .OpBuilder(s"firrtl.dshl", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Dshr[UInt, R] with
  extension (ref: R)
    def >>>(
      that:      Referable[UInt]
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_dshr",
        Droppable,
        // todo: from MLIR.
        ref.tpe,
        ctx.handler
          .OpBuilder(s"firrtl.dshr", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: And[UInt, R] with
  extension (ref: R)
    def &(
      that:      R
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_and",
        Droppable,
        // todo: from MLIR.
        ref.tpe,
        ctx.handler
          .OpBuilder(s"firrtl.and", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Or[UInt, R] with
  extension (ref: R)
    def |(
      that:      R
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_or",
        Droppable,
        // todo: from MLIR.
        ref.tpe,
        ctx.handler
          .OpBuilder(s"firrtl.or", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Xor[UInt, R] with
  extension (ref: R)
    def ^(
      that:      R
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_or",
        Droppable,
        // todo: from MLIR.
        ref.tpe,
        ctx.handler
          .OpBuilder(s"firrtl.xor", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Cat[UInt, R] with
  extension (ref: R)
    def ##(
      that:      R
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_cat",
        Droppable,
        // todo: from MLIR.
        UInt((ref.tpe.width.toInt + that.tpe.width.toInt).W),
        ctx.handler
          .OpBuilder(s"firrtl.cat", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Shl[UInt, R] with
  extension (ref: R)
    def <<(
      that:      Int
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_shl",
        Droppable,
        // todo: from MLIR.
        UInt((ref.tpe.width.toInt + that).W),
        ctx.handler
          .OpBuilder(s"firrtl.shl", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer))
          .withNamedAttrs(
            Seq(("amount", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), that.toLong)))
          )
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Shr[UInt, R] with
  extension (ref: R)
    def >>(
      that:      Int
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_shr",
        Droppable,
        // todo: from MLIR.
        UInt(math.max(ref.tpe.width.toInt - that, 0).W),
        ctx.handler
          .OpBuilder(s"firrtl.shr", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer))
          .withNamedAttrs(
            Seq(("amount", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), that.toLong)))
          )
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Head[UInt, R] with
  extension (ref: R)
    def head(
      that:      Int
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_head",
        Droppable,
        // todo: from MLIR.
        UInt(that.W),
        ctx.handler
          .OpBuilder(s"firrtl.head", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer))
          .withNamedAttrs(
            Seq(("amount", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), that.toLong)))
          )
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Tail[UInt, R] with
  extension (ref: R)
    def tail(
      that:      Int
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_tail",
        Droppable,
        // todo: from MLIR.
        UInt(that.W),
        ctx.handler
          .OpBuilder(s"firrtl.tail", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer))
          .withNamedAttrs(
            Seq(("amount", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), that.toLong)))
          )
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Pad[UInt, R] with
  extension (ref: R)
    def pad(
      that:      Int
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_pad",
        Droppable,
        // todo: from MLIR.
        UInt(math.max(ref.tpe.width.toInt, that).W),
        ctx.handler
          .OpBuilder(s"firrtl.pad", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer))
          .withNamedAttrs(
            Seq(("amount", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), that.toLong)))
          )
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[UInt]]: Bits[UInt, R] with
  extension (ref: R)
    def extract(
      hi:        Int,
      lo:        Int
    )(
      using ctx: Context
    ): Node[UInt] =
      new Node[UInt](
        "_bits",
        Droppable,
        // todo: from MLIR.
        UInt((hi - lo + 1).W),
        ctx.handler
          .OpBuilder(s"firrtl.bits", ctx.currentBlock, ctx.handler.unkLoc)
          .withOperands(Seq(ref.refer))
          .withNamedAttrs(
            Seq(
              ("hi", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), hi.toLong)),
              ("lo", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), lo.toLong))
            )
          )
          .withResultInference(1)
          .build()
          .results
          .head
      )
