package me.jiuyang.zaozi

import me.jiuyang.zaozi.circtlib.MlirValue
import me.jiuyang.zaozi.internal.NameKind.Droppable
import me.jiuyang.zaozi.internal.{Context, firrtl}

object Bits:
  def apply(width: Width): Bits = new Bits(width)

class Bits(val width: Width) extends Data:
  def firrtlType = new firrtl.UInt(width.toInt, false)

trait AsBits[D <: Data, R <: Referable[D]]:
  extension (ref: R)
    def asBits(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bits]

given [R <: Referable[Bits]]: AsBits[Bits, R] with
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

given [R <: Referable[Bits]]: AsUInt[Bits, R] with
  extension (ref: R)
    override def asUInt(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[UInt] =
      val mlirValue: MlirValue = ctx.handler
        .OpBuilder(s"firrtl.asUInt", ctx.currentBlock, SourceLocator(file, line).toMLIR)
        .withOperands(Seq(ref.refer))
        .withResultInference(1)
        .build()
        .results
        .head
      new Node[UInt](
        s"${valName.value}_asUInt",
        Droppable,
        // todo: from MLIR.
        UInt(ref.tpe.width),
        mlirValue
      )

given [R <: Referable[Bits]]: AsBool[Bits, R] with
  extension (ref: R)
    override def asBool(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool] =
      require(ref.tpe.width == 1.W)
      val mlirValue: MlirValue = ctx.handler
        .OpBuilder(s"firrtl.asUInt", ctx.currentBlock, SourceLocator(file, line).toMLIR)
        .withOperands(Seq(ref.refer))
        .withResultInference(1)
        .build()
        .results
        .head
      new Node[Bool](
        s"${valName.value}_asUInt",
        Droppable,
        // todo: from MLIR.
        Bool(),
        mlirValue
      )

given [R <: Referable[Bits]]: AsSInt[Bits, R] with
  extension (ref: R)
    override def asSInt(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[SInt] =
      val mlirValue: MlirValue = ctx.handler
        .OpBuilder(s"firrtl.asSInt", ctx.currentBlock, SourceLocator(file, line).toMLIR)
        .withOperands(Seq(ref.refer))
        .withResultInference(1)
        .build()
        .results
        .head
      new Node[SInt](
        s"${valName.value}_asSInt",
        Droppable,
        // todo: from MLIR.
        // todo: what if width = -1, 0, 1?
        SInt(ref.tpe.width),
        mlirValue
      )

given [R <: Referable[Bits]]: Not[Bits, Bits, R] with
  extension (ref: R)
    override def unary_~(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bits] =
      val mlirValue: MlirValue = ctx.handler
        .OpBuilder(s"firrtl.not", ctx.currentBlock, SourceLocator(file, line).toMLIR)
        .withOperands(Seq(ref.refer))
        .withResultInference(1)
        .build()
        .results
        .head
      new Node[Bits](
        s"${valName.value}_not",
        Droppable,
        ref.tpe,
        mlirValue
      )

given [R <: Referable[Bits]]: AndR[Bits, Bool, R] with
  extension (ref: R)
    override def andR(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool] =
      val mlirValue: MlirValue = ctx.handler
        .OpBuilder(s"firrtl.andr", ctx.currentBlock, SourceLocator(file, line).toMLIR)
        .withOperands(Seq(ref.refer))
        .withResultInference(1)
        .build()
        .results
        .head
      new Node[Bool](
        s"${valName.value}_andR",
        Droppable,
        Bool(),
        mlirValue
      )

given [R <: Referable[Bits]]: OrR[Bits, Bool, R] with
  extension (ref: R)
    override def orR(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool] =
      val mlirValue: MlirValue = ctx.handler
        .OpBuilder(s"firrtl.orr", ctx.currentBlock, SourceLocator(file, line).toMLIR)
        .withOperands(Seq(ref.refer))
        .withResultInference(1)
        .build()
        .results
        .head
      new Node[Bool](
        s"${valName.value}_orR",
        Droppable,
        Bool(),
        mlirValue
      )

given [R <: Referable[Bits]]: XorR[Bits, Bool, R] with
  extension (ref: R)
    override def xorR(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool] =
      val mlirValue: MlirValue = ctx.handler
        .OpBuilder(s"firrtl.xorr", ctx.currentBlock, SourceLocator(file, line).toMLIR)
        .withOperands(Seq(ref.refer))
        .withResultInference(1)
        .build()
        .results
        .head
      new Node[Bool](
        s"${valName.value}_xorR",
        Droppable,
        Bool(),
        mlirValue
      )

given [R <: Referable[Bits]]: Eq[Bits, Bool, R] with
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

given [R <: Referable[Bits]]: Neq[Bits, Bool, R] with
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

given [R <: Referable[Bits]]: And[Bits, Bits, R] with
  extension (ref: R)
    def &(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bits] =
      new Node[Bits](
        s"${valName.value}_and",
        Droppable,
        // todo: from MLIR.
        ref.tpe,
        ctx.handler
          .OpBuilder(s"firrtl.and", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[Bits]]: Or[Bits, Bits, R] with
  extension (ref: R)
    def |(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bits] =
      new Node[Bits](
        s"${valName.value}_or",
        Droppable,
        // todo: from MLIR.
        ref.tpe,
        ctx.handler
          .OpBuilder(s"firrtl.or", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[Bits]]: Xor[Bits, Bits, R] with
  extension (ref: R)
    def ^(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bits] =
      new Node[Bits](
        s"${valName.value}_xor",
        Droppable,
        // todo: from MLIR.
        ref.tpe,
        ctx.handler
          .OpBuilder(s"firrtl.xor", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[Bits]]: Cat[Bits, R] with
  extension (ref: R)
    def ##(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bits] =
      new Node[Bits](
        s"${valName.value}_cat",
        Droppable,
        // todo: from MLIR.
        Bits((ref.tpe.width.toInt + that.tpe.width.toInt).W),
        ctx.handler
          .OpBuilder(s"firrtl.cat", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer, that.refer))
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[Bits]]: Shl[Bits, Int | Referable[UInt], Bits, R] with
  extension (ref: R)
    def <<(
      that:      Int | Referable[UInt]
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bits] =
      that match
        case that: Int             =>
          new Node[Bits](
            s"${valName.value}_shl",
            Droppable,
            // todo: from MLIR.
            Bits((ref.tpe.width.toInt + that).W),
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
          new Node[Bits](
            s"${valName.value}_dshl",
            Droppable,
            // todo: from MLIR.
            Bits((ref.tpe.firrtlType.width.get.toInt + 2 << that.tpe.firrtlType.width.get.toInt - 1).W),
            ctx.handler
              .OpBuilder(s"firrtl.dshl", ctx.currentBlock, SourceLocator(file, line).toMLIR)
              .withOperands(Seq(ref.refer, that.refer))
              .withResultInference(1)
              .build()
              .results
              .head
          )

given [R <: Referable[Bits], THAT <: Int | Referable[UInt]]: Shr[Bits, THAT, Bits, R] with
  extension (ref: R)
    def >>(
      that:      THAT
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bits] =
      that match
        case that: Int             =>
          new Node[Bits](
            s"${valName.value}_shr",
            Droppable,
            // todo: from MLIR.
            Bits(math.max(ref.tpe.width.toInt - that, 0).W),
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
          new Node[Bits](
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

given [R <: Referable[Bits]]: Head[Bits, Int, Bits, R] with
  extension (ref: R)
    def head(
      that:      Int
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bits] =
      new Node[Bits](
        s"${valName.value}_head",
        Droppable,
        // todo: from MLIR.
        Bits(that.W),
        ctx.handler
          .OpBuilder(s"firrtl.head", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer))
          .withNamedAttrs(
            Seq(("amount", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), that.toLong)))
          )
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[Bits]]: Tail[Bits, Int, Bits, R] with
  extension (ref: R)
    def tail(
      that:      Int
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bits] =
      new Node[Bits](
        s"${valName.value}_tail",
        Droppable,
        // todo: from MLIR.
        Bits(that.W),
        ctx.handler
          .OpBuilder(s"firrtl.tail", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer))
          .withNamedAttrs(
            Seq(("amount", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), that.toLong)))
          )
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[Bits]]: Pad[Bits, Int, Bits, R] with
  extension (ref: R)
    def pad(
      that:      Int
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bits] =
      new Node[Bits](
        s"${valName.value}_pad",
        Droppable,
        // todo: from MLIR.
        Bits(math.max(ref.tpe.width.toInt, that).W),
        ctx.handler
          .OpBuilder(s"firrtl.pad", ctx.currentBlock, SourceLocator(file, line).toMLIR)
          .withOperands(Seq(ref.refer))
          .withNamedAttrs(
            Seq(("amount", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), that.toLong)))
          )
          .withResultInference(1)
          .build()
          .results
          .head
      )

given [R <: Referable[Bits]]: ExtractRange[Bits, Int, Bits, R] with
  extension (ref: R)
    def extractRange(
      hi:        Int,
      lo:        Int
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bits] =
      new Node[Bits](
        s"${valName.value}_bits",
        Droppable,
        // todo: from MLIR.
        Bits((hi - lo + 1).W),
        ctx.handler
          .OpBuilder(s"firrtl.bits", ctx.currentBlock, SourceLocator(file, line).toMLIR)
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

given [R <: Referable[Bits], IDX <: Int | Ref[UInt]]: ExtractElement[Bits, Bool, R, IDX] with
  extension (ref: R)
    def extractElement(
      idx:       IDX
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[Bool] =
      idx match
        case idx: Int       =>
          new Node[Bool](
            s"${valName.value}_bits",
            Droppable,
            Bool(),
            ctx.handler
              .OpBuilder(s"firrtl.bits", ctx.currentBlock, SourceLocator(file, line).toMLIR)
              .withOperands(Seq(ref.refer))
              .withNamedAttrs(
                Seq(
                  ("hi", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), idx.toLong)),
                  ("lo", ctx.handler.mlirIntegerAttrGet(ctx.handler.mlirIntegerTypeGet(32), idx.toLong))
                )
              )
              .withResultInference(1)
              .build()
              .results
              .head
          )
        case idx: Ref[UInt] =>
          ???
