// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import org.llvm.mlir.scalalib.capi.ir.{given_LocationApi, Context, Location, LocationApi}

import java.lang.foreign.Arena
import me.jiuyang.zaozi.Parameter
import me.jiuyang.zaozi.HWInterface
import me.jiuyang.zaozi.DVInterface
import org.llvm.mlir.scalalib.capi.ir.Block
import me.jiuyang.zaozi.reftpe.{Const, Interface, Node, Propagated, Referable}
import me.jiuyang.zaozi.valuetpe.Data
import me.jiuyang.zaozi.ConstructorApi
import me.jiuyang.zaozi.InstanceContext
import javax.naming.NameNotFoundException

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
  using sourcecode.Name.Machine,
  InstanceContext
): String = summon[sourcecode.Name.Machine].value match
  case actualName if !sourcecode.Util.isSyntheticName(actualName) => actualName
  case _                                                          => s"_GEN_${summon[InstanceContext].anonSignalCounter.inc()}"

private inline def bundleFieldName(
  using sourcecode.Name.Machine
): String = summon[sourcecode.Name.Machine].value match
  case actualName if !sourcecode.Util.isSyntheticName(actualName) => actualName
  case anonName                                                   => throw NameNotFoundException(s"Cannot find name for BundleField ${anonName}")

/** Wrap an MLIR operation result as Const or Node depending on whether the source reference is Const. */
private[zaozi] def constPropagate[R <: Referable[?], RET <: Data](
  source: R,
  tpe:    RET,
  op:     org.llvm.mlir.scalalib.capi.ir.Operation
): Propagated[R, RET] =
  val result = source match
    case _: Const[?] =>
      new Const[RET]:
        val _tpe:       RET                                      = tpe
        val _operation: org.llvm.mlir.scalalib.capi.ir.Operation = op
    case _ =>
      new Node[RET]:
        val _tpe:       RET                                      = tpe
        val _operation: org.llvm.mlir.scalalib.capi.ir.Operation = op
  result.asInstanceOf[Propagated[R, RET]]
