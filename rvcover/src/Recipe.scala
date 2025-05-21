// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvcover

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.tpe.*

import org.llvm.mlir.scalalib.{Block, Context, Location, LocationApi, Operation, Type, Value, given}

import java.lang.foreign.Arena

//  ============= constraints =================
// TODO: use rvdecoderdb's meta data to generate the constraints
// TODO: the output type of isXXX should be Ref[Bool]

// instructions
// format: off

// base constraints
def hasRd()(using Arena, Context, Block, Index): Unit = smtAssert(summon[Index].rd =/= -1.S)
def hasRs1()(using Arena, Context, Block, Index): Unit = smtAssert(summon[Index].rs1 =/= -1.S)
def hasRs2()(using Arena, Context, Block, Index): Unit = smtAssert(summon[Index].rs2 =/= -1.S)
def hasImm()(using Arena, Context, Block, Index): Unit = smtAssert(summon[Index].imm =/= -2049.S)

def noRd()(using Arena, Context, Block, Index): Unit = smtAssert(summon[Index].rd === -1.S)
def noRs1()(using Arena, Context, Block, Index): Unit = smtAssert(summon[Index].rs1 === -1.S)
def noRs2()(using Arena, Context, Block, Index): Unit = smtAssert(summon[Index].rs2 === -1.S)
def noImm()(using Arena, Context, Block, Index): Unit = smtAssert(summon[Index].imm === -2049.S)

def rdRange(start: Int, end: Int)(using Arena, Context, Block, Index): Unit =
  smtAssert(summon[Index].rd >= start.S & summon[Index].rd < end.S)

def rs1Range(start: Int, end: Int)(using Arena, Context, Block, Index): Unit =
  smtAssert(summon[Index].rs1 >= start.S & summon[Index].rs1 < end.S)

def rs2Range(start: Int, end: Int)(using Arena, Context, Block, Index): Unit =
  smtAssert(summon[Index].rs2 >= start.S & summon[Index].rs2 < end.S)

def immRange(start: Int, end: Int)(using Arena, Context, Block, Index): Unit =
  smtAssert(summon[Index].imm >= start.S & summon[Index].imm < end.S)

// add rd, rs1, rs2
def isAdd()(using Arena, Context, Block, Index): Unit =
  smtAssert(summon[Index].nameId === 0.S)
  hasRd()
  hasRs1()
  hasRs2()
  noImm()

def isAddi()(using Arena, Context, Block, Index): Unit =
  smtAssert(summon[Index].nameId === 1.S)
  hasRd()
  hasRs1()
  noRs2()
  hasImm()
  immRange(-2048, 2048)
  
def isAnd()(using Arena, Context, Block, Index): Unit =
  smtAssert(summon[Index].nameId === 2.S)
  hasRd()
  hasRs1()
  hasRs2()
  noImm()

def isAndi()(using Arena, Context, Block, Index): Unit =
  smtAssert(summon[Index].nameId === 3.S)
  hasRd()
  hasRs1()
  noRs2()
  hasImm()
  immRange(-2048, 2048)

def isAuipc()(using Arena, Context, Block, Index): Unit =
  smtAssert(summon[Index].nameId === 4.S)
  hasRd()
  noRs1()
  noRs2()
  hasImm()
  immRange(-524288, 524288)


// format: on
//  ============= classes =================
case class Index(
  val idx: Int
)(
  using Arena,
  Context,
  Block) {
  // instruction fields
  val nameId = smtValue(s"NameId_${idx}", SInt)
  val rd     = smtValue(s"Rd_${idx}", SInt)
  val rs1    = smtValue(s"Rs1_${idx}", SInt)
  val rs2    = smtValue(s"Rs2_${idx}", SInt)
  val imm    = smtValue(s"Imm_${idx}", SInt)

  override def toString: String =
    s"$idx: $${NameId_${idx}} x$${Rd_${idx}} x$${Rs1_${idx}} x$${Rs2_${idx}} $${Imm_${idx}}"
}

class Recipe(val name: String) {
  private val indices = scala.collection.mutable.Map[Int, Index]()

  def addIndex(idx: Index): Index = {
    indices.getOrElseUpdate(idx.idx, idx)
  }

  override def toString(): String = {
    val indexStrings = indices.values.map(_.toString).mkString("\n")
    s"Recipe: $name\nIndices:\n$indexStrings"
  }
}

def recipe(name: String)(block: Recipe ?=> Unit): Recipe = {
  given Recipe = new Recipe(name)

  block

  summon[Recipe]
}

def index(
  idx:   Int
)(
  using Arena,
  Context,
  Block,
  Recipe
)(block: Index ?=> Unit
): Unit = {
  val index = new Index(idx)
  summon[Recipe].addIndex(index)

  given Index = index

  // default constrains
  rdRange(-1, 32)
  rs1Range(-1, 32)
  rs2Range(-1, 32)
  immRange(-2049, 2048)

  block
}
