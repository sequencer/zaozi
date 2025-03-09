// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package org.llvm.mlir.scalalib.dialect.func

import org.llvm.mlir.scalalib.{Block, Context, HasOperation, Location, Module as MlirModule, Operation, Value, given}

import java.lang.foreign.Arena

class Func(val _operation: Operation)
trait FuncApi extends HasOperation[Func]:
  inline def op(
    symName:     String
    // funcType: Type,
    // symVisibility: String,
    // argAttrs: Seq[NamedAttribute],
    // resAttrs: Seq[NamedAttribute],
    // noInline: Boolean,
  )(
    using arena: Arena,
    context:     Context
  ): Func

  extension (c: Func)
    inline def block(
      using Arena
    ): Block
    inline def appendToModule(
    )(
      using arena: Arena,
      module:      MlirModule
    ): Unit
end FuncApi
