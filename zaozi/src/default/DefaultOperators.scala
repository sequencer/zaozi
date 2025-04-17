// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import org.llvm.mlir.scalalib.{given_LocationApi, Context, Location, LocationApi}

import java.lang.foreign.Arena

private inline def locate(
  using Arena,
  Context,
  sourcecode.File,
  sourcecode.Line
): Location =
  summon[LocationApi].locationFileLineColGet(
    summon[sourcecode.File].value,
    summon[sourcecode.Line].value,
    0
  )

private inline def valName(
  using sourcecode.Name.Machine,
  sourcecode.File,
  sourcecode.Line
): String = summon[sourcecode.Name.Machine].value match
  case actualName if !sourcecode.Util.isSyntheticName(actualName) => actualName
  // TODO: add a mutable state in generator to store the counter
  case _                                                          => "_GEN_${counter}"
