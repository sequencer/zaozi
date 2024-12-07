// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.{*, given}
import utest.*

def firrtlTest[P <: Parameter, I <: Interface[P]](
  parameter:  P,
  interface:  I,
  moduleName: Option[String] = None
)(checkLines: String*
)(body:       me.jiuyang.zaozi.internal.Context ?=> (P, Wire[I]) => Unit
): Unit =
  val out = new StringBuilder
  val ctx = Module(moduleName.getOrElse("NoName"), parameter, interface)(body)
  ctx.handler.mlirExportFIRRTL(ctx.root, out ++= _)
  if (checkLines.isEmpty)
    println(s"please add lines to check for:\n$out")
    assert(false)
  else checkLines.foreach(l => assert(out.toString.contains(l)))
