// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.plugin

import dotty.tools.dotc.core.Symbols.Symbol
import dotty.tools.dotc.util.SourcePosition

import scala.collection.concurrent.TrieMap

/** Represents a bundle field definition (val fieldName = Aligned/Flipped(...)) */
case class BundleFieldDefinition(
  bundleSymbol: Symbol,
  fieldName:    String,
  sourcePos:    SourcePosition,
  isFlipped:    Boolean,
  fieldType:    String)

/** Represents a bundle field usage (io.fieldName access via Dynamic selectDynamic) */
case class BundleFieldUsage(
  bundleSymbol: Symbol,
  fieldName:    String,
  sourcePos:    SourcePosition)

/** Thread-safe registry for collecting bundle field definitions and usages during compilation.
  *
  * This registry is populated by BundleFieldCollectorPhase and consumed by SemanticDBEnhancerPhase.
  */
object BundleFieldRegistry:
  // Thread-safe storage for definitions: bundleSymbol -> List of field definitions
  private val definitions = TrieMap.empty[Symbol, List[BundleFieldDefinition]]

  // Thread-safe storage for usages: source file path -> List of field usages
  private val usages = TrieMap.empty[String, List[BundleFieldUsage]]

  /** Register a bundle field definition.
    *
    * @param bundleSymbol
    *   The symbol of the Bundle class containing this field
    * @param fieldName
    *   The name of the field (val name)
    * @param sourcePos
    *   The source position of the field definition
    * @param isFlipped
    *   Whether the field was defined with Flipped (true) or Aligned (false)
    * @param fieldType
    *   String representation of the field's Data type
    */
  def registerDefinition(
    bundleSymbol: Symbol,
    fieldName:    String,
    sourcePos:    SourcePosition,
    isFlipped:    Boolean,
    fieldType:    String = ""
  ): Unit =
    val defn = BundleFieldDefinition(bundleSymbol, fieldName, sourcePos, isFlipped, fieldType)
    definitions.updateWith(bundleSymbol) {
      case Some(existing) => Some(defn :: existing)
      case None           => Some(List(defn))
    }

  /** Register a bundle field usage.
    *
    * @param bundleSymbol
    *   The symbol of the Bundle class being accessed
    * @param fieldName
    *   The name of the field being accessed
    * @param sourcePos
    *   The source position of the field access
    */
  def registerUsage(
    bundleSymbol: Symbol,
    fieldName:    String,
    sourcePos:    SourcePosition
  ): Unit =
    val usage      = BundleFieldUsage(bundleSymbol, fieldName, sourcePos)
    val sourcePath = sourcePos.source.path
    usages.updateWith(sourcePath) {
      case Some(existing) => Some(usage :: existing)
      case None           => Some(List(usage))
    }

  /** Get all field definitions for a given bundle class. */
  def getDefinitionsFor(bundleSymbol: Symbol): List[BundleFieldDefinition] =
    definitions.getOrElse(bundleSymbol, Nil)

  /** Get all field usages in a given source file. */
  def getUsagesForFile(sourcePath: String): List[BundleFieldUsage] =
    usages.getOrElse(sourcePath, Nil)

  /** Get all registered bundle symbols that have definitions. */
  def getAllBundleSymbols: Iterable[Symbol] =
    definitions.keys

  /** Get all registered definitions. */
  def getAllDefinitions: Iterable[BundleFieldDefinition] =
    definitions.values.flatten

  /** Clear the registry (useful between compilation runs). */
  def clear(): Unit =
    definitions.clear()
    usages.clear()

  /** Get summary statistics for debugging. */
  def stats: String =
    s"BundleFieldRegistry: ${definitions.size} bundles, ${definitions.values.map(_.size).sum} definitions, ${usages.values.map(_.size).sum} usages"
