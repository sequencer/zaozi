package me.jiuyang.zaozi.alter

import me.jiuyang.zaozi.valuetpe.Data
import me.jiuyang.zaozi.reftpe.Referable
import me.jiuyang.zaozi.StrictMonoConnect
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.Context
import org.llvm.mlir.scalalib.Block
import org.llvm.circt.scalalib.firrtl.operation.MatchingConnectApi
import org.llvm.circt.scalalib.firrtl.operation.InvalidValueApi
import org.llvm.circt.scalalib.firrtl.operation.given
import org.llvm.mlir.scalalib.Location
import org.llvm.mlir.scalalib.LocationApi
import org.llvm.mlir.scalalib.{
  given_AttributeApi,
  given_BlockApi,
  given_IdentifierApi,
  given_LocationApi,
  given_NamedAttributeApi,
  given_OperationApi,
  given_RegionApi,
  given_TypeApi,
  given_ValueApi,
  Block,
  Context,
  Location,
  LocationApi,
  Operation,
  Type,
  Value
}
import me.jiuyang.zaozi.default.given

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

private inline def valName(
  using sourcecode.Name
): String = summon[sourcecode.Name].value

// TODO: split LHS & RHS into two different trait? this might help for Vec static accessing assignment.
given [D <: Data, SRC <: Referable[D], SINK <: Referable[D]]: MonoConnect[D, SRC, SINK] with
  extension (ref: SINK)
    def :=(
      that: SRC
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line
    ): Unit =
      summon[ConnectApi]
        .op(
          that.refer,
          ref.refer,
          locate
        )
        .operation
        .appendToBlock()
    def dontCare(
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line
    ): Unit =
      val invalidOp = summon[InvalidValueApi]
        .op(
          ref.refer.getType,
          locate
        )
      invalidOp.operation.appendToBlock()
      summon[ConnectApi]
        .op(
          invalidOp.result,
          ref.refer,
          locate
        )
        .operation
        .appendToBlock()
