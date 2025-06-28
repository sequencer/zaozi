// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvcover.tests

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.tpe.*
import me.jiuyang.smtlib.parser.{parseZ3Output, Z3Status}
import me.jiuyang.smtlib.*

import org.llvm.mlir.scalalib.capi.dialect.func.{Func, FuncApi, given}
import org.llvm.mlir.scalalib.capi.dialect.func.DialectApi as FuncDialect
import org.llvm.mlir.scalalib.capi.dialect.func.given_DialectApi
import org.llvm.mlir.scalalib.capi.dialect.smt.DialectApi as SmtDialect
import org.llvm.mlir.scalalib.capi.dialect.smt.given_DialectApi
import org.llvm.mlir.scalalib.capi.target.exportsmtlib.given_ExportSmtlibApi
import org.llvm.mlir.scalalib.capi.ir.{Block, Context, ContextApi, LocationApi, Module, ModuleApi, Value, given}

import java.lang.foreign.Arena

import utest.*

def getModelField(model: Map[String, Boolean | BigInt], name: String): Int =
  model
    .get(name)
    .map {
      case b: Boolean => throw new RuntimeException(s"Expected an integer for $name, but got a boolean: $b")
      case i: BigInt  => i.toInt
    }
    .getOrElse(
      throw new RuntimeException(s"Model does not contain field: $name")
    )

def rvcoverTest(body: (Arena, Context, Block) ?=> Unit): Unit =
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
    smtCheck
  }

  // output smtlib
  val out = new StringBuilder
  summon[Module].exportSMTLIB(out ++= _)
  summon[Context].destroy()
  summon[Arena].close()

  val smt = out.toString.replace("(reset)", "(get-model)")

  val z3Output = os
    .proc("z3", "-in", "-t:1000")
    .call(
      stdin = smt,
      check = false // ignore the error message when `unknown` or `unsat`
    )

  val z3Result = parseZ3Output(z3Output.out.text())
  // todo: handling unsat status in the future
  z3Result.status ==> Z3Status.Sat
  val model    = z3Result.model

  val instructions      = getInstructions()
  val instructionCounts = 2

  // todo: move it to the Recipe class defination
  // fix: output bits directly 
  (0 until instructionCounts).foreach { i =>
    val nameId = getModelField(model, s"nameId_$i")
    val inst   = instructions(nameId)
    val name   = inst.name
    val args   = inst.args.map { arg =>
      val argName: String = translateToCamelCase(arg.name)
      val argNameLowered = argName.head.toLower + argName.tail
      val prefix         = if arg.name.startsWith("r") then "x" else ""
      prefix + getModelField(model, argNameLowered + s"_$i").toString()
    }
    println(s"Instruction $i: $name ${args.mkString(" ")}")
    println(s"Instruction $i: " + inst.toString)
  }
