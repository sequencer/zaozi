// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.plugin

import dotty.tools.dotc.plugins.ResearchPlugin
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Phases.Phase

/** Zaozi SemanticDB Enhancement Plugin
  *
  * This ResearchPlugin enhances SemanticDB output with source information for bundle fields, enabling IDE features like
  * go-to-definition and find-references for dynamically-accessed bundle fields.
  *
  * The plugin inserts two phases:
  *   - BundleFieldCollectorPhase: Runs after posttyper to collect bundle field definitions and usages
  *   - SemanticDBEnhancerPhase: Runs after extractSemanticDB to inject additional symbols and occurrences
  */
class ZaoziSemanticDBPlugin extends ResearchPlugin:
  val name:                 String = "zaozi-semanticdb"
  override val description: String = "Enhances SemanticDB with bundle field source info for zaozi hardware DSL"

  /** Initialize the plugin by modifying the compiler phase plan.
    *
    * ResearchPlugin API allows us to directly modify the phase plan, inserting our custom phases at the appropriate
    * positions in the compilation pipeline.
    */
  override def init(
    options: List[String],
    plan:    List[List[Phase]]
  )(
    using Context
  ): List[List[Phase]] =
    val collectorPhase = BundleFieldCollectorPhase()
    val enhancerPhase  = SemanticDBEnhancerPhase()

    // Insert phases into the plan
    insertPhases(plan, collectorPhase, enhancerPhase)

  /** Insert custom phases into the compiler phase plan.
    *
    * @param plan
    *   The current phase plan
    * @param collector
    *   The BundleFieldCollectorPhase to insert after posttyper
    * @param enhancer
    *   The SemanticDBEnhancerPhase to insert after extractSemanticDB
    * @return
    *   Modified phase plan with custom phases inserted
    */
  private def insertPhases(
    plan:      List[List[Phase]],
    collector: BundleFieldCollectorPhase,
    enhancer:  SemanticDBEnhancerPhase
  ): List[List[Phase]] =
    // Insert phases in their own groups (to avoid fusion issues)
    plan.flatMap { phaseGroup =>
      val hasPosttyper         = phaseGroup.exists(_.phaseName == "posttyper")
      val hasExtractSemanticDB = phaseGroup.exists(_.phaseName == "extractSemanticDBAppendDiagnostics")

      if hasPosttyper then
        // Add collector as a separate phase group after posttyper group
        List(phaseGroup, List(collector))
      else if hasExtractSemanticDB then
        // Add enhancer as a separate phase group after extractSemanticDB group
        List(phaseGroup, List(enhancer))
      else List(phaseGroup)
    }
