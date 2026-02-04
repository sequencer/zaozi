// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import me.jiuyang.zaozi.{nameHierarchy, LayerTree, ProbeDefine}
import me.jiuyang.zaozi.reftpe.Referable
import me.jiuyang.zaozi.valuetpe.{CanProbe, Data, RProbe, RWProbe}

import org.llvm.circt.scalalib.dialect.firrtl.operation.{RefCastApi, RefDefineApi, RefSendApi, given}
import org.llvm.mlir.scalalib.capi.ir.{Block, Context, given}

import java.lang.foreign.Arena

given [D <: Data & CanProbe, P <: RWProbe[D] | RProbe[D], SRC <: Referable[D], SINK <: Referable[P]]
  : ProbeDefine[D, P, SRC, SINK] with
  extension (ref: SINK)
    def <==(
      that: SRC
    )(
      using Arena,
      Context,
      Block,
      LayerTree,
      sourcecode.File,
      sourcecode.Line
    ): Unit =
      val refSendOp   = summon[RefSendApi]
        .op(
          that.refer,
          locate
        )
      val refCastOp   = summon[RefCastApi]
        .op(refSendOp.result, ref.refer.getType, locate)
      val refDefineOp = summon[RefDefineApi]
        .op(
          ref.refer,
          refCastOp.result,
          locate
        )
      refSendOp.operation.appendToBlock()
      refCastOp.operation.appendToBlock()
      refDefineOp.operation.appendToBlock()
