// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvcover.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.tpe.*
import me.jiuyang.smtlib.*

import org.llvm.mlir.scalalib.dialect.func.{Func, FuncApi, given}
import org.llvm.mlir.scalalib.dialect.smt.capi.{given_DialectHandleApi, given_ModuleApi}
import org.llvm.mlir.scalalib.{Block, Context, ContextApi, LocationApi, Module, ModuleApi, Value, given}

import org.chipsalliance.rvdecoderdb.{Encoding, Instruction, InstructionSet}
import os.Path
import java.io.{File, FileWriter}

import java.lang.foreign.Arena

// set the instruction set
def getInstructions(): Seq[Instruction] =
  val riscvOpcodesPath: Path = Path(
    sys.env.getOrElse(
      "RISCV_OPCODES_INSTALL_PATH",
      throw new RuntimeException("Environment variable RISCV_OPCODES_INSTALL_PATH not set")
    )
  )
  org.chipsalliance.rvdecoderdb
    .instructions(riscvOpcodesPath)
    .filter(instruction =>
      (Seq("rv_i", "rv_zicsr", "rv_zifencei", "rv_system")).contains(instruction.instructionSet.name)
    )
    .toSeq
    .filter {
      // special case for rv32 pseudo from rv64
      case i if i.pseudoFrom.isDefined && Seq("slli", "srli", "srai").contains(i.name) => true
      case i if i.pseudoFrom.isDefined                                                 => false
      case _                                                                           => true
    }
    .sortBy(i => (i.instructionSet.name, i.name))

// set argLut
def getArgLut(): Seq[(String, org.chipsalliance.rvdecoderdb.Arg)] =
  val riscvOpcodesPath: Path = Path(
    sys.env.getOrElse(
      "RISCV_OPCODES_INSTALL_PATH",
      throw new RuntimeException("Environment variable RISCV_OPCODES_INSTALL_PATH not set")
    )
  )
  org.chipsalliance.rvdecoderdb
    .argLut(riscvOpcodesPath)
    .toSeq
    .sortBy(i => (i._1, i._2.name))

// helper function
def translateToCamelCase(s: String): String =
  s.replace(".", "_")
    .split("[^a-zA-Z0-9]")
    .filter(_.nonEmpty)
    .map(_.capitalize)
    .mkString

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
  summon[Context].loadSmtDialect()
  summon[Context].loadFuncDialect()

  // Then based on the module to construct the Func.func .
  given Module = summon[ModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
  given Func   = summon[FuncApi].op("func")
  given Block  = summon[Func].block
  summon[Func].appendToModule()

  // main wrapper for the test body
  solver {
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
