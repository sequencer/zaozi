// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvcover.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.tpe.*
import me.jiuyang.smtlib.*

import org.llvm.mlir.scalalib.capi.dialect.func.{Func, FuncApi, given}
import org.llvm.mlir.scalalib.capi.dialect.smt.DialectApi as SmtDialect
import org.llvm.mlir.scalalib.capi.dialect.smt.given_DialectApi
import org.llvm.mlir.scalalib.capi.dialect.func.DialectApi as FuncDialect
import org.llvm.mlir.scalalib.capi.dialect.func.given_DialectApi
import org.llvm.mlir.scalalib.capi.target.exportsmtlib.given_ExportSmtlibApi
import org.llvm.mlir.scalalib.capi.ir.{Block, Context, ContextApi, LocationApi, Module, ModuleApi, Value, given}

import org.chipsalliance.rvdecoderdb.{Encoding, Instruction, InstructionSet}
import os.Path
import java.io.{File, FileWriter}

import java.lang.foreign.Arena

def rvcoverTest(body: (Arena, Context, Block) ?=> Unit): Unit =
  // prepare instruction map
  val instWriter = new FileWriter(new File("./output.inst"))
  getInstructions().foreach { case instruction =>
    instWriter.write(s"${instruction.name}")
    instruction.args.foreach { arg =>
      val argName: String = translateToCamelCase(arg.name)
      instWriter.write(s", $argName")
    }
    instWriter.write("\n")
  }
  instWriter.close()

  // prepare argLut map
  val argLutWriter = new FileWriter(new File("./output.argLut"))
  getArgLut().foreach { case (name, _) =>
    argLutWriter.write(s"${translateToCamelCase(name)}\n")
  }
  argLutWriter.close()

  // prepare the Context
  given Arena   = Arena.ofConfined()
  given Context = summon[ContextApi].contextCreate
  summon[SmtDialect].loadDialect()
  summon[FuncDialect].loadDialect()

  // Then based on the module to construct the Func.func .
  given Module = summon[ModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
  given Func   = summon[FuncApi].op("func")
  given Block  = summon[Func].block
  summon[Func].appendToModule()

  // main wrapper for the test body
  solver {
    smtSetLogic("QF_LIA")
    body
  }

  // output smtlib
  val out = new StringBuilder
  summon[Module].exportSMTLIB(out ++= _)
  summon[Context].destroy()
  summon[Arena].close()

  println(out.toString)

  // output file
  val writer = new FileWriter(new File("./output.smt2"), true)
  writer.write(out.toString.replace("(reset)", "(check-sat)\n(get-model)"))
  writer.close()
