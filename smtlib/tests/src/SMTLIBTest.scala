// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.smtlib.tests

import me.jiuyang.smtlib.{*, given}
import me.jiuyang.smtlib.default.{*, given}

import org.llvm.mlir.scalalib.dialect.func.{Func, FuncApi, given}
import org.llvm.mlir.scalalib.dialect.smt.capi.{given_DialectHandleApi, given_ModuleApi}
import org.llvm.mlir.scalalib.{Block, Context, ContextApi, LocationApi, Module, ModuleApi, Value, given}

import java.io.{File, FileWriter}

import java.lang.foreign.Arena

def smtTest(checkLines: String*)(body: (Arena, Context, Block) ?=> Unit): Unit =
  given Arena   = Arena.ofConfined()
  given Context = summon[ContextApi].contextCreate
  summon[Context].loadSmtDialect()
  summon[Context].loadFuncDialect()

  // Then based on the module to construct the Func.func .
  given Module = summon[ModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
  given Func   = summon[FuncApi].op("func")
  given Block  = summon[Func].block
  summon[Func].appendToModule()

  body

  // dump mlir
  summon[Func].operation.dump()
  val out = new StringBuilder
  summon[Module].exportSMTLIB(out ++= _)
  summon[Context].destroy()
  summon[Arena].close()

  // output smtlib2 to file
  println(out.toString)
  val writer = new FileWriter(new File("./output.smt2"), true)
  writer.write(out.toString.replace("(reset)", "(get-model)"))
  writer.close()

  // check the output
  if (checkLines.isEmpty)
    assert(out.toString == "Nothing To Check")
  else checkLines.foreach(l => assert(out.toString.contains(l)))
