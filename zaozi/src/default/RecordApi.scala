// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.magic.UntypedDynamicSubfield
import me.jiuyang.zaozi.reftpe.{Ref, Referable}
import me.jiuyang.zaozi.valuetpe.{Data, ProbeRecord, Record}

import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

import java.lang.foreign.Arena

given [T <: Record | ProbeRecord, R <: Referable[T]]: RecordApi[T, R] with
  extension (ref: R)
    def field[T <: Data](
      fieldName: String
    )(
      using Arena,
      Block,
      Context,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine
    ): Ref[T] = ref._tpe.getUntypedRefViaFieldValName(ref.refer, fieldName).asInstanceOf[Ref[T]]

end given
