// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.plugin

import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Phases.Phase
import dotty.tools.dotc.core.Symbols.*
import dotty.tools.dotc.semanticdb.*
import dotty.tools.dotc.semanticdb.{TextDocument, TextDocuments}
import dotty.tools.io.AbstractFile

import java.nio.file.{Files, Path, Paths}
import scala.util.{Failure, Success, Try}

/** Compiler phase that enhances SemanticDB output with bundle field information.
  *
  * This phase runs after extractSemanticDB and:
  *   1. Reads the generated .semanticdb files
  *   2. Replaces selectDynamic occurrences with bundle field references
  *   3. Injects additional SymbolInformation for bundle field definitions
  *   4. Writes the enhanced .semanticdb files back
  *
  * This enables IDE features like go-to-definition and find-references for dynamically-accessed bundle fields.
  */
class SemanticDBEnhancerPhase extends Phase:
  override def phaseName: String = "zaozi-semanticdb-enhancer"

  override def run(
    using ctx: Context
  ): Unit =
    val unit          = ctx.compilationUnit
    val sourcePath    = unit.source.path
    val sourceContent = new String(unit.source.content())
    val sourceLines   = sourceContent.split("\n", -1) // -1 to keep trailing empty lines

    // Get collected bundle field definitions
    val allDefinitions = BundleFieldRegistry.getAllDefinitions.toList

    // Only process if we have bundle field definitions
    if allDefinitions.isEmpty then return

    // Create symbol information for field definitions in this file
    val definitionsInFile = allDefinitions.filter(_.sourcePos.source.path == sourcePath)
    val newSymbolInfos    = definitionsInFile.map(d =>
      createSymbolInformation(d)(
        using ctx
      )
    )

    // Build a map of field names to their bundle symbols for lookup
    val fieldToBundleMap: Map[String, List[BundleFieldDefinition]] =
      allDefinitions.groupBy(_.fieldName)

    // Try to find and modify the SemanticDB file
    findSemanticDBFile(unit.source.file) match
      case Some(semanticdbPath) =>
        modifySemanticDBFile(semanticdbPath, sourceLines, fieldToBundleMap, newSymbolInfos)
      case None                 =>
        // SemanticDB file not found - this is expected if -Ysemanticdb is not enabled
        ()

  /** Find the SemanticDB file for a given source file. */
  private def findSemanticDBFile(
    sourceFile: AbstractFile
  )(
    using ctx:  Context
  ): Option[Path] =
    val settings  = ctx.settings
    val outputDir = settings.outputDir.value.path

    Try {
      val sourceRoot   = settings.sourceroot.value
      val sourcePath   = Paths.get(sourceFile.path)
      val relativePath =
        if sourceRoot.nonEmpty then Paths.get(sourceRoot).relativize(sourcePath)
        else sourcePath.getFileName

      val semanticdbDir  = Paths.get(outputDir).resolve("META-INF").resolve("semanticdb")
      val semanticdbFile = semanticdbDir.resolve(relativePath.toString + ".semanticdb")

      if Files.exists(semanticdbFile) then Some(semanticdbFile)
      else None
    }.getOrElse(None)

  /** Check if a symbol is a Dynamic method (selectDynamic, applyDynamic, etc.) */
  private def isDynamicMethodSymbol(symbol: String): Boolean =
    symbol.contains("selectDynamic") ||
      symbol.contains("applyDynamic") ||
      symbol.contains("applyDynamicNamed") ||
      symbol.contains("updateDynamic")

  /** Extract the field name from source text at a given range. */
  private def extractFieldNameFromSource(sourceLines: Array[String], range: Range): Option[String] =
    Try {
      if range.startLine >= 0 && range.startLine < sourceLines.length then
        val line = sourceLines(range.startLine)
        if range.startCharacter >= 0 && range.endCharacter <= line.length then
          val fieldName = line.substring(range.startCharacter, range.endCharacter)
          // Validate it looks like an identifier
          if fieldName.matches("[a-zA-Z_][a-zA-Z0-9_]*") then Some(fieldName)
          else None
        else None
      else None
    }.getOrElse(None)

  /** Read, modify, and write back the SemanticDB file. */
  private def modifySemanticDBFile(
    path:             Path,
    sourceLines:      Array[String],
    fieldToBundleMap: Map[String, List[BundleFieldDefinition]],
    newSymbolInfos:   List[SymbolInformation]
  )(
    using ctx:        Context
  ): Unit =
    Try {
      // Read existing SemanticDB file
      val bytes = Files.readAllBytes(path)
      val docs  = TextDocuments.parseFrom(bytes)

      // Modify each document in the file
      val modifiedDocs = docs.documents.map { doc =>
        // Replace Dynamic method occurrences with bundle field references
        val modifiedOccurrences = doc.occurrences.map { occ =>
          if isDynamicMethodSymbol(occ.symbol) then
            occ.range match
              case Some(range) =>
                // Extract the field name from source at this position
                extractFieldNameFromSource(sourceLines, range) match
                  case Some(fieldName) =>
                    // Look up the bundle field definition
                    fieldToBundleMap.get(fieldName) match
                      case Some(definitions) if definitions.nonEmpty =>
                        // Use the first matching definition (could be improved with type context)
                        val defn   = definitions.head
                        val symbol = createSymbolString(defn.bundleSymbol, fieldName)
                        SymbolOccurrence(
                          range = Some(range),
                          symbol = symbol,
                          role = SymbolOccurrence.Role.REFERENCE
                        )
                      case _                                         =>
                        // No matching definition, keep original
                        occ
                  case None            =>
                    // Couldn't extract field name, keep original
                    occ
              case None        =>
                occ
          else occ
        }

        doc.copy(
          occurrences = modifiedOccurrences,
          symbols = doc.symbols ++ newSymbolInfos
        )
      }

      // Write back
      val modifiedTextDocs = TextDocuments(modifiedDocs)
      Files.write(path, modifiedTextDocs.toByteArray)
    } match
      case Success(_) => ()
      case Failure(e) =>
        // Log error but don't fail compilation
        ()

  /** Create a SemanticDB symbol string for a bundle field. */
  private def createSymbolString(
    bundleSymbol: Symbol,
    fieldName:    String
  )(
    using Context
  ): String =
    val bundlePath = bundleSymbol.showFullName.replace('.', '/')
    s"$bundlePath#$fieldName."

  /** Create a SymbolInformation for a bundle field definition. */
  private def createSymbolInformation(
    defn: BundleFieldDefinition
  )(
    using Context
  ): SymbolInformation =
    val symbol = createSymbolString(defn.bundleSymbol, defn.fieldName)
    SymbolInformation(
      symbol = symbol,
      language = Language.SCALA,
      kind = SymbolInformation.Kind.FIELD,
      properties = 0,
      displayName = defn.fieldName,
      signature = Signature.Empty,
      annotations = Nil,
      access = Access.Empty,
      overriddenSymbols = Nil
    )
