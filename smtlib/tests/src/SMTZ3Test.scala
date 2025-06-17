// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.smtlib.tests

import me.jiuyang.smtlib.{*, given}
import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.parser.parseZ3Output

import org.llvm.mlir.scalalib.capi.dialect.func.{Func, FuncApi, given}
import org.llvm.mlir.scalalib.capi.dialect.smt.DialectApi as SmtDialect
import org.llvm.mlir.scalalib.capi.dialect.smt.given_DialectApi
import org.llvm.mlir.scalalib.capi.dialect.func.DialectApi as FuncDialect
import org.llvm.mlir.scalalib.capi.dialect.func.given_DialectApi
import org.llvm.mlir.scalalib.capi.target.exportsmtlib.given_ExportSmtlibApi
import org.llvm.mlir.scalalib.capi.ir.{Block, Context, ContextApi, LocationApi, Module, ModuleApi, Value, given}
import utest.*

import java.io.{File, FileWriter}

import java.lang.foreign.Arena

def smtZ3Test(body: (Arena, Context, Block) ?=> Unit): Seq[(String, Boolean | Int)] =
  given Arena   = Arena.ofConfined()
  given Context = summon[ContextApi].contextCreate
  summon[SmtDialect].loadDialect()
  summon[FuncDialect].loadDialect()

  // Then based on the module to construct the Func.func .
  given Module = summon[ModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
  given Func   = summon[FuncApi].op("func")
  given Block  = summon[Func].block
  summon[Func].appendToModule()

  solver {
    body
  }

  val out = new StringBuilder
  summon[Module].exportSMTLIB(out ++= _)
  summon[Context].destroy()
  summon[Arena].close()

  val smt = out.toString.replace("(reset)", "(check-sat)\n(get-model)")

  val z3Output = os
    .proc("z3", "-in", "-t:1000")
    .call(
      stdin = smt,
      check = false // ignore the error message when `unknown` or `unsat`
    )

  parseZ3Output(z3Output.out.text())
