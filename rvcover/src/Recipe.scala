// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvcover

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.tpe.*
import org.chipsalliance.rvdecoderdb.*
import os.Path

import java.lang.foreign.Arena

import org.llvm.mlir.scalalib.{Block, Context, given}

sealed trait Variable {
  private var _constraints: List[Ref[Bool]] = List()

  def name:  String
  def value: Ref[SInt]

  def constraints: List[Ref[Bool]] = _constraints

  def addConstraint(constraint: Ref[Bool]): Unit =
    _constraints = _constraints :+ constraint

}

case class Imm(
  bits: Int
)(
  using Arena,
  Context,
  Block,
  sourcecode.File,
  sourcecode.Line,
  sourcecode.Name)
    extends Variable:
  val name:  String    = "imm"
  val value: Ref[SInt] = smtValue(name, SInt)

  addConstraint(value >= 0.S)
  addConstraint(value < (1 << bits).S)

case class Rd(
)(
  using Arena,
  Context,
  Block,
  sourcecode.File,
  sourcecode.Line,
  sourcecode.Name)
    extends Variable:
  val name:  String    = "rd"
  val value: Ref[SInt] = smtValue(name, SInt)

  addConstraint(value > 0.S)
  addConstraint(value < 32.S)

case class Rs1(
)(
  using Arena,
  Context,
  Block,
  sourcecode.File,
  sourcecode.Line,
  sourcecode.Name)
    extends Variable:
  val name:  String    = "rs1"
  val value: Ref[SInt] = smtValue(name, SInt)

  addConstraint(value > 0.S)
  addConstraint(value < 32.S)

case class Rs2(
)(
  using Arena,
  Context,
  Block,
  sourcecode.File,
  sourcecode.Line,
  sourcecode.Name)
    extends Variable:
  val name:  String    = "rs2"
  val value: Ref[SInt] = smtValue(name, SInt)

  addConstraint(value > 0.S)
  addConstraint(value < 32.S)

case class Inst(
  name: String,
  variables: List[Variable] = List()):

  override def toString(): String =
    val riscvOpcodesPath: Path                  = Path(
      sys.env.getOrElse(
        "RISCV_OPCODES_INSTALL_PATH",
        throw new RuntimeException("Environment variable RISCV_OPCODES_INSTALL_PATH not set")
      )
    )
    val instTable:        Iterable[Instruction] = instructions(riscvOpcodesPath)

    val args = instTable
      .find(_.name == name)
      .getOrElse(throw new RuntimeException(s"Instruction $name not found"))
      .args

    val argsPattern = args.map { arg =>
      arg.name match
        case "rd"  => "x$rd"
        case "rs1" => "x$rs1"
        case "rs2" => "x$rs2"
        case "imm" => "$imm"
        case _     => arg.name
    }.mkString(", ")

    s"${name} ${argsPattern}"

  def cook(
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Unit =
    variables.foreach { variable => variable.constraints.foreach { constraint => smtAssert(constraint) } }

case class Recipe(
  name: String):
  private var constraints: List[Ref[Bool]] = List()
  private var insts:       List[Inst]      = List()

  def addConstraint(constraint: Ref[Bool]): Unit =
    constraints = constraints :+ constraint

  def addInstruction(inst: Inst): Unit = insts = insts :+ inst

  override def toString(): String = insts.map(_.toString).mkString("\n")

  def cook(
  )(
    using Arena,
    Context,
    Block,
    sourcecode.File,
    sourcecode.Line,
    sourcecode.Name
  ): Unit = insts.foreach(_.cook())
