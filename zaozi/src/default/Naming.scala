// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import org.llvm.mlir.scalalib.{given_LocationApi, Context, Location, LocationApi}

import java.lang.foreign.Arena
import me.jiuyang.zaozi.Parameter
import me.jiuyang.zaozi.HWInterface
import me.jiuyang.zaozi.DVInterface
import org.llvm.mlir.scalalib.Block
import me.jiuyang.zaozi.reftpe.Interface
import org.llvm.circt.scalalib.firrtl.operation.Module
import me.jiuyang.zaozi.ConstructorApi
import me.jiuyang.zaozi.InstanceContext
import javax.naming.NameNotFoundException

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
  InstanceContext
): String = summon[sourcecode.Name.Machine].value match
  case actualName if !sourcecode.Util.isSyntheticName(actualName) => actualName
  case _                                                          => s"_GEN_${summon[InstanceContext].anonSignalCounter.inc()}"

private inline def bundleFieldName(
  using sourcecode.Name.Machine
): String = summon[sourcecode.Name.Machine].value match
  case actualName if !sourcecode.Util.isSyntheticName(actualName) => actualName
  case anonName                                                   => throw NameNotFoundException(s"Cannot find name for BundleField ${anonName}")
