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
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Const[UInt] =
      val tpe     = UInt(width)
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
      new Const(const, UInt(width))

given ToConstUInt[Int] with
  extension (ref: Int)
    def U(
      width:     Width
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Const[UInt] = BigInt(ref).U(width)

given [R <: Referable[UInt]]: AsBits[UInt, R] with
  extension (ref: R)
    override def asBits(
                         using ctx: Context,
                         file: sourcecode.File,
                         line: sourcecode.Line,
                         valName: sourcecode.Name
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

given [R <: Referable[UInt]]: AsUInt[UInt, R] with
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
        ref.tpe,
        mlirValue
      )

given [R <: Referable[UInt]]: AsSInt[UInt, R] with
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

given [R <: Referable[UInt]]: Cvt[UInt, R] with
  extension (ref: R)
    override def zext(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[SInt] =
      val mlirValue: MlirValue = ctx.handler
        .OpBuilder(s"firrtl.cvt", ctx.currentBlock, SourceLocator(file, line).toMLIR)
        .withOperands(Seq(ref.refer))
        .withResultInference(1)
        .build()
        .results
        .head
      new Node[SInt](
        s"${valName.value}_cvt",
        Droppable,
        // todo: from MLIR.
        // todo: what if width = -1, 0, 1?
        if (ref.tpe.width.unknown) SInt(-1.W) else SInt((ref.tpe.width.toInt + 1).W),
        mlirValue
      )

given [R <: Referable[UInt]]: Add[UInt, R] with
  extension (ref: R)
    def +(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[UInt] =
      new Node[UInt](
        s"${valName.value}_add",
        Droppable,
        // todo: from MLIR.
        UInt((math.max(ref.tpe.firrtlType.width.get.toInt, that.tpe.firrtlType.width.get.toInt) + 1).W),
        ctx.handler
          .OpBuilder(s"firrtl.add", ctx.currentBlock, SourceLocator(file, line).toMLIR)
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
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[UInt] =
      new Node[UInt](
        s"${valName.value}_sub",
        Droppable,
        // todo: from MLIR.
        UInt((math.max(ref.tpe.firrtlType.width.get.toInt, that.tpe.firrtlType.width.get.toInt) + 1).W),
        ctx.handler
          .OpBuilder(s"firrtl.sub", ctx.currentBlock, SourceLocator(file, line).toMLIR)
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
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[UInt] =
      new Node[UInt](
        s"${valName.value}_mul",
        Droppable,
        // todo: from MLIR.
        UInt((ref.tpe.firrtlType.width.get.toInt + that.tpe.firrtlType.width.get.toInt).W),
        ctx.handler
          .OpBuilder(s"firrtl.mul", ctx.currentBlock, SourceLocator(file, line).toMLIR)
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
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[UInt] =
      new Node[UInt](
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

given [R <: Referable[UInt]]: Rem[UInt, R] with
  extension (ref: R)
    def %(
      that:      R
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[UInt] =
      new Node[UInt](
        s"${valName.value}_rem",
        Droppable,
        // todo: from MLIR.
        UInt(math.min(ref.tpe.firrtlType.width.get.toInt, that.tpe.firrtlType.width.get.toInt).W),
        ctx.handler
          .OpBuilder(s"firrtl.rem", ctx.currentBlock, SourceLocator(file, line).toMLIR)
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

given [R <: Referable[UInt]]: Leq[UInt, R] with
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

given [R <: Referable[UInt]]: Gt[UInt, R] with
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

given [R <: Referable[UInt]]: Geq[UInt, R] with
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

given [R <: Referable[UInt]]: Eq[UInt, R] with
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

given [R <: Referable[UInt]]: Neq[UInt, R] with
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

given [R <: Referable[UInt]]: Dshl[UInt, R] with
  extension (ref: R)
    def <<<(
      that:      Referable[UInt]
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[UInt] =
      new Node[UInt](
        s"${valName.value}_dshl",
        Droppable,
        // todo: from MLIR.
        UInt((ref.tpe.firrtlType.width.get.toInt + 2 << that.tpe.firrtlType.width.get.toInt - 1).W),
        ctx.handler
          .OpBuilder(s"firrtl.dshl", ctx.currentBlock, SourceLocator(file, line).toMLIR)
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
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[UInt] =
      new Node[UInt](
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

given [R <: Referable[UInt]]: Shl[UInt, R] with
  extension (ref: R)
    def <<(
      that:      Int
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[UInt] =
      new Node[UInt](
        s"${valName.value}_shl",
        Droppable,
        // todo: from MLIR.
        UInt((ref.tpe.width.toInt + that).W),
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

given [R <: Referable[UInt]]: Shr[UInt, R] with
  extension (ref: R)
    def >>(
      that:      Int
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[UInt] =
      new Node[UInt](
        s"${valName.value}_shr",
        Droppable,
        // todo: from MLIR.
        UInt(math.max(ref.tpe.width.toInt - that, 0).W),
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

given [R <: Referable[UInt]]: Head[UInt, R] with
  extension (ref: R)
    def head(
      that:      Int
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[UInt] =
      new Node[UInt](
        s"${valName.value}_head",
        Droppable,
        // todo: from MLIR.
        UInt(that.W),
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

given [R <: Referable[UInt]]: Tail[UInt, R] with
  extension (ref: R)
    def tail(
      that:      Int
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[UInt] =
      new Node[UInt](
        s"${valName.value}_tail",
        Droppable,
        // todo: from MLIR.
        UInt(that.W),
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

given [R <: Referable[UInt]]: Pad[UInt, R] with
  extension (ref: R)
    def pad(
      that:      Int
    )(
      using ctx: Context,
      file:      sourcecode.File,
      line:      sourcecode.Line,
      valName:   sourcecode.Name
    ): Node[UInt] =
      new Node[UInt](
        s"${valName.value}_pad",
        Droppable,
        // todo: from MLIR.
        UInt(math.max(ref.tpe.width.toInt, that).W),
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