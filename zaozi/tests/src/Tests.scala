// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.tests

import me.jiuyang.zaozi.{*, given}
import os.ProcessOutput
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

def verilogTest[P <: Parameter, I <: Interface[P]](
                                                   parameter:  P,
                                                   interface:  I,
                                                   moduleName: Option[String] = None
                                                 )(checkLines: String*
                                                 )(body:       me.jiuyang.zaozi.internal.Context ?=> (P, Wire[I]) => Unit
                                                 ): Unit =
  val firtoolIn = new StringBuilder
  val out = new StringBuilder
  val ctx = Module(moduleName.getOrElse("NoName"), parameter, interface)(body)
  ctx.handler.mlirExportFIRRTL(ctx.root, firtoolIn ++= _)
  os.proc("firtool", "-format=fir").call(stdin = firtoolIn.toString, stdout = ProcessOutput.Readlines(str => out ++= s"$str\n"))
  if (checkLines.isEmpty)
    println(s"please add lines to check for:\n$out")
    assert(false)
  else checkLines.foreach(l => assert(out.toString.contains(l)))
