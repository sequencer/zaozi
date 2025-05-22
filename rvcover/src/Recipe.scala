// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvcover

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.tpe.*

import org.llvm.mlir.scalalib.{Block, Context, Location, LocationApi, Operation, Type, Value, given}

import java.lang.foreign.Arena

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

  block
}
