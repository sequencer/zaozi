// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.plugin

import dotty.tools.dotc.ast.tpd.*
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Phases.Phase
import dotty.tools.dotc.core.Symbols.*
import dotty.tools.dotc.core.Types.*
import dotty.tools.dotc.core.Constants.Constant
import dotty.tools.dotc.core.Names.*

/** Compiler phase that collects bundle field definitions and usages.
  *
  * This phase runs after posttyper and before extractSemanticDB. It traverses the typed AST to:
  *   1. Find classes extending Bundle and extract their field definitions (Aligned/Flipped calls)
  *   2. Find usages of bundle fields (selectDynamic calls that get expanded)
  *
  * All collected information is stored in BundleFieldRegistry for later use by SemanticDBEnhancerPhase.
  */
class BundleFieldCollectorPhase extends Phase:
  override def phaseName: String = "zaozi-bundle-collector"

  override def run(
    using ctx: Context
  ): Unit =
    val unit = ctx.compilationUnit
    val tree = unit.tpdTree

    // Traverse the tree to collect definitions and usages
    val collector = BundleFieldCollector()
    collector.traverse(tree)

  /** Tree traverser that collects bundle field information. */
  private class BundleFieldCollector extends TreeTraverser:
    override def traverse(
      tree: Tree
    )(
      using Context
    ): Unit =
      tree match
        // Detect Bundle class definitions
        case typeDef @ TypeDef(name, template: Template) if isBundleClass(typeDef.symbol) =>
          collectBundleFields(typeDef.symbol, template)
          traverseChildren(tree)

        // Detect selectDynamic calls - these are the original field accesses
        // The tree looks like: io.selectDynamic("fieldName") or after inlining
        // it becomes getRefViaFieldValName calls
        case apply @ Apply(select @ Select(receiver, methodName), args)
            if methodName.toString == "selectDynamic" && args.nonEmpty =>
          args.head match
            case Literal(Constant(fieldName: String)) =>
              collectSelectDynamicUsage(apply, receiver, fieldName)
            case _                                    => ()
          traverseChildren(tree)

        // Also detect getRefViaFieldValName calls (from macro expansion)
        // Pattern: receiver.getRefViaFieldValName[T](referValue)("fieldName")
        case apply @ Apply(
              Apply(TypeApply(Select(receiver, methodName), _), _),
              List(Literal(Constant(fieldName: String)))
            ) if isFieldAccessMethod(methodName.toString) =>
          collectFieldUsageFromMacro(apply, receiver, fieldName)
          traverseChildren(tree)

        // Alternative pattern without type arguments
        case apply @ Apply(
              Apply(Select(receiver, methodName), _),
              List(Literal(Constant(fieldName: String)))
            ) if isFieldAccessMethod(methodName.toString) =>
          collectFieldUsageFromMacro(apply, receiver, fieldName)
          traverseChildren(tree)

        case _ =>
          traverseChildren(tree)

    /** Check if a class symbol extends Bundle. */
    private def isBundleClass(
      sym: Symbol
    )(
      using Context
    ): Boolean =
      sym.info.baseClasses.exists { base =>
        base.showFullName == "me.jiuyang.zaozi.valuetpe.Bundle"
      }

    /** Check if a method name is a bundle field access method. */
    private def isFieldAccessMethod(name: String): Boolean =
      name == "getRefViaFieldValName" || name == "getOptionRefViaFieldValName"

    /** Collect field definitions from a Bundle class template. */
    private def collectBundleFields(
      bundleSymbol: Symbol,
      template:     Template
    )(
      using Context
    ): Unit =
      template.body.foreach {
        case valDef @ ValDef(fieldName, tpt, rhs) =>
          rhs match
            // Match: val fieldName = this.Aligned[T](arg)(implicit) - with TypeApply
            case Apply(Apply(TypeApply(Select(This(_), methodName), _), args), _) if methodName.toString == "Aligned" =>
              BundleFieldRegistry.registerDefinition(
                bundleSymbol = bundleSymbol,
                fieldName = fieldName.toString,
                sourcePos = valDef.sourcePos,
                isFlipped = false,
                fieldType = extractFieldType(args)
              )

            case Apply(Apply(TypeApply(Select(This(_), methodName), _), args), _) if methodName.toString == "Flipped" =>
              BundleFieldRegistry.registerDefinition(
                bundleSymbol = bundleSymbol,
                fieldName = fieldName.toString,
                sourcePos = valDef.sourcePos,
                isFlipped = true,
                fieldType = extractFieldType(args)
              )

            // Match: val fieldName = Aligned(...) - without this prefix
            case Apply(Select(_, methodName), args) if methodName.toString == "Aligned" =>
              BundleFieldRegistry.registerDefinition(
                bundleSymbol = bundleSymbol,
                fieldName = fieldName.toString,
                sourcePos = valDef.sourcePos,
                isFlipped = false,
                fieldType = extractFieldType(args)
              )

            // Match: val fieldName = Flipped(...)
            case Apply(Select(_, methodName), args) if methodName.toString == "Flipped" =>
              BundleFieldRegistry.registerDefinition(
                bundleSymbol = bundleSymbol,
                fieldName = fieldName.toString,
                sourcePos = valDef.sourcePos,
                isFlipped = true,
                fieldType = extractFieldType(args)
              )

            // Match: val fieldName = this.Aligned(...) or this.Flipped(...) - without TypeApply
            case Apply(Apply(Select(This(_), methodName), args), _)
                if methodName.toString == "Aligned" || methodName.toString == "Flipped" =>
              BundleFieldRegistry.registerDefinition(
                bundleSymbol = bundleSymbol,
                fieldName = fieldName.toString,
                sourcePos = valDef.sourcePos,
                isFlipped = methodName.toString == "Flipped",
                fieldType = extractFieldType(args)
              )

            case _ => // Not an Aligned/Flipped call

        case _ => // Not a ValDef
      }

    /** Extract the field type from Aligned/Flipped arguments. */
    private def extractFieldType(
      args: List[Tree]
    )(
      using Context
    ): String =
      args.headOption.map(_.tpe.widen.show).getOrElse("")

    /** Collect a field usage from a selectDynamic call. */
    private def collectSelectDynamicUsage(
      apply:     Apply,
      receiver:  Tree,
      fieldName: String
    )(
      using Context
    ): Unit =
      // The receiver is the Referable[T] - extract T to get the bundle type
      extractBundleFromReferable(receiver).foreach { bundleSymbol =>
        BundleFieldRegistry.registerUsage(
          bundleSymbol = bundleSymbol,
          fieldName = fieldName,
          sourcePos = apply.sourcePos
        )
      }

    /** Collect a field usage from a getRefViaFieldValName call (macro expansion). */
    private def collectFieldUsageFromMacro(
      apply:     Apply,
      receiver:  Tree,
      fieldName: String
    )(
      using Context
    ): Unit =
      // The receiver after macro expansion is typically: ref._tpe.asInstanceOf[DynamicSubfield]
      extractBundleSymbol(receiver).foreach { bundleSymbol =>
        BundleFieldRegistry.registerUsage(
          bundleSymbol = bundleSymbol,
          fieldName = fieldName,
          sourcePos = apply.sourcePos
        )
      }

    /** Extract the Bundle symbol from a Referable[T] receiver. */
    private def extractBundleFromReferable(
      receiver: Tree
    )(
      using Context
    ): Option[Symbol] =
      receiver.tpe.widen match
        case AppliedType(tycon, args) if args.nonEmpty =>
          // Referable[T] - T is the bundle type
          val bundleType = args.head
          Some(bundleType.typeSymbol).filter(_.exists)
        case _                                         =>
          None

    /** Extract the Bundle symbol from a receiver expression (macro expanded). */
    private def extractBundleSymbol(
      receiver: Tree
    )(
      using Context
    ): Option[Symbol] =
      // The receiver after macro expansion is typically:
      // ref._tpe.asInstanceOf[DynamicSubfield]
      // We need to trace back to find the bundle type

      receiver.tpe.widen match
        case AppliedType(tycon, args) if args.nonEmpty =>
          // Look for the Data type argument
          args.headOption.map(_.typeSymbol)
        case tpe                                       =>
          // Try to get the type symbol directly
          Some(tpe.typeSymbol).filter(_.exists)
