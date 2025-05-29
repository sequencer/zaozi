// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Rui Huang <vowstar@gmail.com>

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.magic.macros.generator
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

case class ClockDomain(name: String)
given upickle.default.ReadWriter[ClockDomain] = upickle.default.macroRW
case class ResetDomain(name: String, asynchronous: Boolean, activeLow: Boolean)
given upickle.default.ReadWriter[ResetDomain] = upickle.default.macroRW
case class PowerDomain(name: String, alwaysOn: Boolean)
given upickle.default.ReadWriter[PowerDomain] = upickle.default.macroRW
case class ClockToClockConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[ClockToClockConstraint] = upickle.default.macroRW
case class ClockToResetConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[ClockToResetConstraint] = upickle.default.macroRW
case class ClockToPowerConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[ClockToPowerConstraint] = upickle.default.macroRW
case class ResetToClockConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[ResetToClockConstraint] = upickle.default.macroRW
case class ResetToResetConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[ResetToResetConstraint] = upickle.default.macroRW
case class ResetToPowerConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[ResetToPowerConstraint] = upickle.default.macroRW
case class PowerToClockConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[PowerToClockConstraint] = upickle.default.macroRW
case class PowerToResetConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[PowerToResetConstraint] = upickle.default.macroRW
case class PowerToPowerConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[PowerToPowerConstraint] = upickle.default.macroRW

case class PRCMParameter(
  clocks:                 Seq[ClockDomain],
  resets:                 Seq[ResetDomain],
  powers:                 Seq[PowerDomain],
  clockToClockConstraint: Seq[ClockToClockConstraint],
  clockToResetConstraint: Seq[ClockToResetConstraint],
  clockToPowerConstraint: Seq[ClockToPowerConstraint],
  resetToClockConstraint: Seq[ResetToClockConstraint],
  resetToResetConstraint: Seq[ResetToResetConstraint],
  resetToPowerConstraint: Seq[ResetToPowerConstraint],
  powerToClockConstraint: Seq[PowerToClockConstraint],
  powerToResetConstraint: Seq[PowerToResetConstraint],
  powerToPowerConstraint: Seq[PowerToPowerConstraint])
    extends Parameter:
  val clockCounts = clocks.size
  val resetCounts = resets.size
  val powerCounts = powers.size

given upickle.default.ReadWriter[PRCMParameter] = upickle.default.macroRW

class PRCMLayers(parameter: PRCMParameter) extends LayerInterface(parameter)

class ClockBundle extends Bundle:
  val request = Flipped(Bool())
  val stable  = Flipped(Bool())
  val enable  = Aligned(Bool())

class ResetBundle extends Bundle:
  val request = Flipped(Bool())
  val enable  = Aligned(Bool())

class PowerBundle extends Bundle:
  val request = Flipped(Bool())
  val good    = Flipped(Bool())
  val enable  = Aligned(Bool())
  val isolate = Aligned(Bool())

class PRCMIO(parameter: PRCMParameter) extends HWInterface(parameter):
  val aonClock = Flipped(Clock())
  val aonReset = Flipped(Reset())

  val clock = Aligned(Vec(parameter.clockCounts, new ClockBundle))
  val reset = Aligned(Vec(parameter.resetCounts, new ResetBundle))
  val power = Aligned(Vec(parameter.powerCounts, new PowerBundle))

class PRCMProbe(parameter: PRCMParameter) extends DVInterface[PRCMParameter, PRCMLayers](parameter)

@generator
object PRCMModule extends Generator[PRCMParameter, PRCMLayers, PRCMIO, PRCMProbe]:
  def architecture(parameter: PRCMParameter) =
    val io = summon[Interface[PRCMIO]]
