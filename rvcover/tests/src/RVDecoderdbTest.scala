// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvcover.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.tpe.*
import me.jiuyang.rvcover.*

import org.chipsalliance.rvdecoderdb.*
import os.Path

import utest.*

import java.lang.foreign.Arena

// parse rvdecoderdb to get instructions & argLut & extensions

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
    .argLut(riscvOpcodesPath, None)
    .toSeq
    .sortBy(i => (i._1, i._2.name))

def getExtensions(): Seq[String] =
  val riscvOpcodesPath: Path = Path(
    sys.env.getOrElse(
      "RISCV_OPCODES_INSTALL_PATH",
      throw new RuntimeException("Environment variable RISCV_OPCODES_INSTALL_PATH not set")
    )
  )
  org.chipsalliance.rvdecoderdb
    .instructions(riscvOpcodesPath)
    .toSeq
    .map(_.instructionSets)
    .flatMap(_.map(_.name))
    .distinct
    .sorted

// helper function
def translateToCamelCase(s: String): String =
  s.replace(".", "_")
    .split("[^a-zA-Z0-9]")
    .filter(_.nonEmpty)
    .map(_.capitalize)
    .mkString

object InstructionTest extends TestSuite:
  val tests = Tests:
    test("import rvdecoderdb success"):
      val riscvOpcodesPath: Path                  = Path(
        sys.env.getOrElse(
          "RISCV_OPCODES_INSTALL_PATH",
          throw new RuntimeException("Environment variable RISCV_OPCODES_INSTALL_PATH not set")
        )
      )
      val instTable:        Iterable[Instruction] = instructions(riscvOpcodesPath)
      // instTable.foreach(println)
      instTable.nonEmpty ==> true
    test("getInstructions() returns non-empty list"):
      val instructions = getInstructions()
      instructions.nonEmpty ==> true
      // println(instructions.map(_.name).mkString(", "))
    test("getArgLut() returns non-empty list"):
      val argLut = getArgLut()
      argLut.nonEmpty ==> true
      // println(argLut.map(_._1).mkString(", "))
    test("getExtensions() returns non-empty list"):
      val extensions = getExtensions()
      extensions.nonEmpty ==> true
      // println(extensions.mkString(", "))
