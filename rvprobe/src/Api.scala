// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvprobe

import me.jiuyang.smtlib.default.{*, given}
import me.jiuyang.smtlib.tpe.*

import org.llvm.mlir.scalalib.capi.ir.{Block, Context, Location, LocationApi, Operation, Type, Value, given}

import java.lang.foreign.Arena

// todo: remove recipe api, use new Recipe directly
def recipe(
  name:  String,
  sets:  Recipe ?=> Ref[Bool]*
)(
  using Arena,
  Context,
  Block
)(block: Recipe ?=> Unit
): Recipe = {
  given Recipe = new Recipe(name)

  // assert sets are valid
  val includedSets: List[Ref[Bool]] = sets.toList.map(f =>
    f(
      using summon[Recipe]
    )
  )
  includedSets.foreach { set =>
    smtAssert(set)
  }
  // assert that sets are mutually exclusive
  val excludedSets = summon[Recipe].allSets.diff(includedSets)
  excludedSets.foreach { set =>
    smtAssert(!set)
  }

  block

  summon[Recipe]
}

// create an instruction with given index
def instruction(
  idx:   Int
)(
  using Arena,
  Context,
  Block,
  Recipe
)(block: Index ?=> Ref[Bool]
): Unit = {
  val index = new Index(idx)
  summon[Recipe].addIndex(index)

  given Index = index

  smtAssert(block)
}

// get an instruction with given index
def instruction(
  idx:   Int
)(
  using Arena,
  Context,
  Block,
  Recipe
): Index = summon[Recipe].getIndex(idx)
