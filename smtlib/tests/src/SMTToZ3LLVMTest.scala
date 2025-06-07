// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.smtlib.tests

import me.jiuyang.smtlib.{*, given}
import me.jiuyang.smtlib.default.{*, given}

import org.llvm.mlir.scalalib.capi.dialect.func.{Func, FuncApi, given}
import org.llvm.mlir.scalalib.capi.dialect.smt.DialectApi as SmtDialect
import org.llvm.mlir.scalalib.capi.dialect.smt.given_DialectApi
import org.llvm.mlir.scalalib.capi.dialect.func.DialectApi as FuncDialect
import org.llvm.mlir.scalalib.capi.dialect.func.given_DialectApi
import org.llvm.mlir.scalalib.capi.target.exportsmtlib.given_ExportSmtlibApi
import org.llvm.mlir.scalalib.capi.ir.{Block, Context, ContextApi, LocationApi, Module, ModuleApi, Value, given}
import org.llvm.mlir.scalalib.capi.pass.{given_PassManagerApi, PassManager, PassManagerApi}

import org.llvm.circt.scalalib.capi.conversion.{
  given_ConversionCreateApi,
  given_ConversionRegisterApi,
  ConversionCreateApi,
  ConversionRegisterApi
}

import java.io.{File, FileWriter}

import java.lang.foreign.Arena

def smtToZ3llvmTest(checkLines: String*)(body: (Arena, Context, Block) ?=> Unit): Unit =
  given Arena   = Arena.ofConfined()
  given Context = summon[ContextApi].contextCreate
  summon[SmtDialect].loadDialect()
  summon[FuncDialect].loadDialect()

  // Then based on the module to construct the Func.func .
  given Module = summon[ModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
  given Func   = summon[FuncApi].op("func")
  given Block  = summon[Func].block
  summon[Func].appendToModule()

  given PassManager = summon[PassManagerApi].passManagerCreate
  summon[PassManager].addOwnedPass(summon[ConversionCreateApi].lowerSMTToZ3LLVM)

  solver {
    body
  }

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
