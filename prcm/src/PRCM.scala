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

/**
 * Clock-to-Clock Constraint: Defines directed dependencies between clock domains
 *
 * Purpose: Ensures proper clock sequencing and hierarchy in SoC power management
 * - Models parent-child clock relationships (e.g., PLL outputs depend on reference clocks)
 * - Enforces clock enablement order (derived clocks cannot start before source clocks)
 * - Prevents clock domain isolation violations
 *
 * Formal Constraint Expression: C_source = False → C_derived = False
 * Meaning: When source clock is disabled, all derived clocks must be disabled
 * Primary scenarios: PLL reference dependencies, clock hierarchy enforcement
 *
 * Constraint Classification: HARD CONSTRAINT
 * Critical for clock system stability and preventing timing violations that could
 * cause system malfunction, data corruption, or permanent damage to clock infrastructure
 *
 * Application Conditions:
 * - When one clock derives from another (PLL lockup dependencies)
 * - Cross-hierarchy clock gating scenarios
 * - Clock domain crossing synchronization requirements
 *
 * Violation Consequences:
 * - Clock instability and metastability in derived domains
 * - PLL unlock conditions leading to system malfunction
 * - Timing violations in cross-domain logic
 * - Potential data corruption in clock domain crossings
 */
case class ClockToClockConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[ClockToClockConstraint] = upickle.default.macroRW

/**
 * Clock-to-Reset Constraint: Defines dependencies between clock domains and reset signals
 *
 * Purpose: Ensures synchronous reset release and prevents metastable reset conditions
 * - Enforces that synchronous resets can only be released when target clocks are stable
 * - Prevents reset release without proper clock presence (C=0 ⇒ R=1 constraint)
 * - Maintains reset domain integrity across power/clock transitions
 *
 * Formal Constraint Expression: C_j = False → R_k = True
 * Meaning: When target clock is stopped, synchronous reset must remain asserted
 * Primary scenarios: Synchronous reset domains, clock-dependent reset release
 *
 * Constraint Classification: HARD CONSTRAINT
 * Essential for preventing metastable reset release that could cause unpredictable
 * system behavior, initialization failures, or permanent logic corruption
 *
 * Application Conditions:
 * - Synchronous reset domains requiring clock-synchronized reset deassertion
 * - Clock-dependent reset release sequences (e.g., PLL lock-dependent resets)
 * - Cross-domain reset synchronization scenarios
 *
 * Violation Consequences:
 * - Metastable reset release causing unpredictable logic states
 * - Setup/hold violations during reset deassertion
 * - Partial reset release leading to inconsistent module initialization
 * - System hang or corruption due to improper reset sequencing
 */
case class ClockToResetConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[ClockToResetConstraint] = upickle.default.macroRW

/**
 * Clock-to-Power Constraint: Defines dependencies between clock domains and power domains
 *
 * Purpose: Models scenarios where clock activity influences power domain control
 * - Clock-driven voltage regulation dependencies
 * - Power island control based on clock activity status
 *
 * Formal Constraint Expression: C_j = True → P_i = True (theoretical)
 * Meaning: Clock activity ideally requires corresponding power domain active
 * Primary scenarios: Activity-based power management, clock-controlled voltage scaling
 * Reality: Most designs allow P_i = False while C_j = True for operational flexibility
 *
 * Constraint Classification: SOFT CONSTRAINT
 * Primarily for power optimization rather than functional safety - violations
 * cause power inefficiency but do not threaten system functionality or integrity
 *
 * Application Conditions:
 * - Clock-controlled power management (activity-based power gating)
 * - Voltage islands requiring specific clock sequences for power transitions
 * - Clock-synchronized power switch control
 *
 * Violation Consequences:
 * - Unnecessary power consumption from clock activity during power transitions
 *   (clock trees continue switching while target power domains are shut down,
 *   leading to wasted dynamic power but minimal system impact - this constraint
 *   is primarily for power optimization rather than functional safety, making
 *   it a soft constraint where violations cause inefficiency but not system
 *   failure or damage)
 */
case class ClockToPowerConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[ClockToPowerConstraint] = upickle.default.macroRW

/**
 * Reset-to-Clock Constraint: Defines dependencies between reset signals and clock domains
 *
 * Purpose: Prevents clock enablement when reset conditions are active
 * - Ensures clocks remain disabled during reset assertion periods
 * - Protects clock generation devices (PLL/DLL/HSI/LSI) from improper reset sequences
 * - Prevents additional power consumption caused by clock activity during reset
 * - Maintains safe reset domain isolation
 *
 * Formal Constraint Expressions:
 * 1. HARD: R_k = False → C_j = True (reset released implies clock enabled)
 *    Critical for clock generation device protection and proper startup sequences
 * 2. SOFT: R_k = True → C_j = False (reset asserted implies clock disabled)
 *    Power optimization only - rarely enforced in practice due to operational conflicts
 *
 * Constraint Classification:
 * - HARD CONSTRAINT: R=0 ⇒ C=1 (reset released implies clock enabled)
 *   Critical for protecting clock generation devices (PLL/DLL/HSI/LSI) from
 *   improper reset sequences that could cause permanent clock generation failures
 * - SOFT CONSTRAINT: R=1 ⇒ C=0 (reset asserted implies clock disabled)
 *   Power optimization only - prevents unnecessary clock activity during reset
 *   but poses no functional safety risk as reset assertion maintains system safety
 *
 * Application Conditions:
 * - Clock source device protection (PLL/DLL reset coordination) - PRIMARY USE CASE
 * - Clock generation infrastructure requiring ordered reset/enable sequences
 * - Reset-gated clock enablement scenarios (mainly for R=0⇒C=1 direction)
 * - Cross-domain reset isolation requirements (when specifically needed)
 * - Power optimization scenarios (R=1⇒C=0 direction - rarely implemented due to
 *   operational conflicts and minimal benefit in practice)
 *
 * Violation Consequences:
 * - Incorrect reset of clock-dependent devices (e.g., PLL/DLL/HSI/LSI) leading
 *   to clock generation failures (critical functional failure requiring system
 *   restart or reconfiguration - most severe violation with immediate system
 *   impact and no graceful degradation possible)
 * - Clock activity during reset causing minor power consumption increase
 *   (soft constraint violation with minimal impact - most designs intentionally
 *   allow clock activity during reset for operational reasons and typically
 *   do not enforce R=1⇒C=0 constraint in practice)
 */
case class ResetToClockConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[ResetToClockConstraint] = upickle.default.macroRW

/**
 * Reset-to-Reset Constraint: Defines hierarchical dependencies between reset domains
 *
 * Purpose: Establishes reset domain hierarchy and sequencing requirements
 * - Parent-child reset relationships (child resets depend on parent reset release)
 * - Reset priority and cascade ordering
 * - Cross-domain reset synchronization chains
 *
 * Formal Constraint Expression: R_parent = True → R_child = True
 * Meaning: When parent reset is asserted, all child resets must remain asserted
 * Primary scenarios: Hierarchical reset trees, reset cascade sequences
 *
 * Constraint Classification: HARD CONSTRAINT
 * Critical for proper system initialization and preventing reset-related deadlocks
 * that could cause system hang or inconsistent module states
 *
 * Application Conditions:
 * - Hierarchical reset trees with ordered release sequences
 * - Multi-level reset domain architectures
 * - Reset synchronization across power/clock domains
 *
 * Violation Consequences:
 * - Out-of-order reset release causing system instability
 * - Reset domain isolation failures
 * - Inconsistent initialization across dependent modules
 * - Potential deadlock in reset release sequences
 */
case class ResetToResetConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[ResetToResetConstraint] = upickle.default.macroRW

/**
 * Reset-to-Power Constraint: Defines dependencies between reset signals and power domains
 *
 * Purpose: Prevents power domain operations during active reset conditions
 * - Ensures reset assertion prevents power domain state changes
 * - Maintains safe power transitions by keeping dependent domains in reset
 *
 * Formal Constraint Expression: R_k = True → P_i = False (theoretical)
 * Meaning: Reset assertion ideally prevents power domain activation
 * Primary scenarios: Reset-locked power sequences, power transition safety
 * Reality: Most designs allow P_i = True while R_k = True as reset maintains safety
 *
 * Constraint Classification: SOFT CONSTRAINT
 * Power optimization focused - reset assertion maintains system safety regardless
 * of power domain activity, making violations non-critical for system functionality
 *
 * Application Conditions:
 * - Reset-locked power management sequences
 * - Cross-domain reset isolation during power transitions
 * - Reset-priority power control systems
 *
 * Violation Consequences:
 * - Unexpected power consumption during reset assertion (additional switching
 *   power in power management circuits and isolation cells while reset remains
 *   active - system stays in safe state but violates power optimization goals,
 *   this constraint is considered soft and non-critical as reset assertion
 *   maintains system safety regardless of power domain activity)
 */
case class ResetToPowerConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[ResetToPowerConstraint] = upickle.default.macroRW

/**
 * Power-to-Clock Constraint: Defines fundamental dependencies between power and clock domains
 *
 * Purpose: Enforces the basic rule that clocks cannot operate without power supply
 * - Implements the fundamental constraint P=0 ⇒ C=0 (power OFF implies clock OFF)
 * - Prevents unpowered clock generation and distribution
 * - Ensures clock domain isolation during power transitions
 *
 * Formal Constraint Expression: P_i = False → C_j = False
 * Meaning: When power domain is off, all clocks in that domain must be disabled
 * Primary scenarios: Power-gated clock domains, cross-domain clock isolation
 * This is the most fundamental constraint in power management systems
 *
 * Constraint Classification: HARD CONSTRAINT
 * Fundamental safety constraint preventing hardware damage and system malfunction
 * from unpowered clock operations - violations can cause permanent damage
 *
 * Application Conditions:
 * - All clock domains require at least one power domain to be active
 * - Cross-power-domain clock distribution scenarios
 * - Power-gated clock source dependencies
 *
 * Violation Consequences:
 * - Floating or undefined clock signals in unpowered domains
 * - Clock distribution network instability
 * - Potential damage to unpowered clock buffers/gates
 * - Metastable conditions in clock domain crossings
 * - System malfunction due to invalid clock states
 */
case class PowerToClockConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[PowerToClockConstraint] = upickle.default.macroRW

/**
 * Power-to-Reset Constraint: Defines dependencies between power domains and reset signals
 *
 * Purpose: Ensures proper reset assertion during power domain transitions
 * - Implements the rule P=0 ⇒ R=1 (power OFF implies reset assertion)
 * - Maintains reset integrity during power cycling
 * - Prevents undefined logic states during power transitions
 *
 * Formal Constraint Expression: P_i = False → R_k = True
 * Meaning: When power domain is off, target reset must be asserted (active)
 * Primary scenarios: Power domain shutdown sequences, unpowered logic protection
 * Essential for preventing floating logic states in unpowered domains
 *
 * Constraint Classification: HARD CONSTRAINT
 * Essential for preventing undefined logic states and data corruption during
 * power transitions - violations can cause system initialization failures
 *
 * Application Conditions:
 * - Power domain shutdown requiring reset assertion
 * - Cross-power-domain reset source dependencies
 * - Always-on reset sources for power-gated domains
 *
 * Violation Consequences:
 * - Undefined logic states in unpowered domains without reset
 * - State corruption during power domain transitions
 * - Reset source unavailability leading to uncontrolled logic
 * - Potential latch-up conditions during power cycling
 * - System initialization failures after power restoration
 */
case class PowerToResetConstraint(from: String, to: String, description: Option[String])
given upickle.default.ReadWriter[PowerToResetConstraint] = upickle.default.macroRW

/**
 * Power-to-Power Constraint: Defines hierarchical dependencies between power domains
 *
 * Purpose: Establishes power domain hierarchy and sequencing requirements
 * - Parent-child power relationships (child domains depend on parent domains)
 * - Power-up/power-down sequencing to prevent voltage conflicts
 * - Power domain isolation and dependency management
 *
 * Formal Constraint Expression: P_parent = False → P_child = False
 * Meaning: When parent power domain is off, all child domains must be off
 * Primary scenarios: Voltage regulator hierarchies, power island dependencies
 * Critical for preventing electrical conflicts in power distribution networks
 *
 * Constraint Classification: HARD CONSTRAINT
 * Critical for preventing voltage conflicts and electrical damage to power
 * infrastructure - violations can cause permanent hardware damage or system failure
 *
 * Application Conditions:
 * - Hierarchical power trees with ordered power-up sequences
 * - Voltage regulator dependencies (derived supplies depend on primary supplies)
 * - Power island architectures with controlled isolation
 *
 * Violation Consequences:
 * - Voltage conflicts between power domains
 * - Power domain isolation failures
 * - Electrical stress on power distribution networks
 * - Potential damage to voltage regulators
 * - System startup failures due to improper power sequencing
 * - Power domain deadlock conditions
 */
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
