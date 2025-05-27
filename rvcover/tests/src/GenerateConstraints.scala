// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvcover.tests

import org.chipsalliance.rvdecoderdb.{Encoding, Instruction, InstructionSet}
import os.Path
import java.io.{File, FileWriter}
import utest.*

// TODO:move to package.mill in the future(but here are some runtime information)
// TODO:use json to organize the output files

object GenerateConstraints extends TestSuite:
  val tests = Tests:
    val writer = new FileWriter(new File("./ConstraintsGenerated.scala"))
    val riscvOpcodesPath: Path = Path(
      sys.env.getOrElse(
        "RISCV_OPCODES_INSTALL_PATH",
        throw new RuntimeException("Environment variable RISCV_OPCODES_INSTALL_PATH not set")
      )
    )

    // ======================================================================================================
    // def amoopRange(start: Int, end: Int)(using Arena, Context, Block, Index): Ref[Bool] = summon[Index].amoop >= start.S & summon[Index].amoop < end.S
    // ======================================================================================================
    getArgLut().foreach { case (name, arg) =>
      // camelCase the argument name
      val argName: String = translateToCamelCase(name)
      val argNameLowered = argName.head.toLower + argName.tail

      writer.write(
        s"def ${argNameLowered}Range(start: Int, end: Int)(using Arena, Context, Block, Index): Ref[Bool] = summon[Index].${argNameLowered} >= start.S & summon[Index].${argNameLowered} < end.S\n"
      )
    }

    writer.write("\n")

    // ======================================================================================================
    // def hasAmoop()(using Arena, Context, Block, Index): Ref[Bool] = amoopRange(0, 32)
    // ======================================================================================================
    getArgLut().foreach { case (name, arg) =>
      // camelCase the argument name
      val argName: String = translateToCamelCase(name)
      val argNameLowered = argName.head.toLower + argName.tail
      writer.write(
        s"def has$argName()(using Arena, Context, Block, Index): Ref[Bool] = ${argNameLowered}Range(0, ${1 << (arg.msb - arg.lsb + 1)})\n"
      )
    }

    writer.write("\n")

    // ======================================================================================================
    // def nameId(idx: Int)(using Arena, Context, Block, Index): Ref[Bool] = summon[Index].nameId === idx.S
    // ======================================================================================================
    writer.write(
      "def nameId(idx: Int)(using Arena, Context, Block, Index): Ref[Bool] = summon[Index].nameId === idx.S\n"
    )

    // ======================================================================================================
    // def isAdd()(using Arena, Context, Block, Index): Ref[Bool] = nameId(0) & hasRd() & hasRs1() & hasRs2() & isRVI()
    // ======================================================================================================
    getInstructions().zipWithIndex.foreach { case (instruction, idx) =>
      // CamelCase the instruction name
      val name = translateToCamelCase(instruction.name)

      val suffix = name match {
        case "Slli" => instruction.instructionSet.name.replace("_", "").toUpperCase()
        case "Srai" => instruction.instructionSet.name.replace("_", "").toUpperCase()
        case "Srli" => instruction.instructionSet.name.replace("_", "").toUpperCase()
        case _      => ""
      }

      writer.write(s"def is${name}${suffix}()(using Arena, Context, Block, Index, Recipe): Ref[Bool] = nameId($idx)")
      instruction.args.foreach { arg =>
        // CamelCase the argument name
        val argName = translateToCamelCase(arg.name)
        writer.write(s" & has$argName()")
      }

      val sets = instruction.instructionSets
        .map(_.name)                                         // e.g., "rv_i", "rv_zicsr", etc.
        .map("is" + _.replace("_", "").toUpperCase() + "()") // e.g., "isRVI()", "isRVZICSR()", etc.

      val s =
        if (sets.length == 1) sets.mkString(" | ") // If there's only one extension, just return join it with " | "
        else sets.mkString("(", " | ", ")")        // If there are multiple extensions, join them with "( | )"

      writer.write(s" & ${s}\n")
    }
    
    writer.write("\n")

    // ======================================================================================================
    // def isRVA()(using Arena, Context, Block, Recipe): Ref[Bool] = summon[Recipe].rv_a
    // ======================================================================================================
    getExtensions().foreach { ext =>
      val extName = ext.replace("_", "").toUpperCase()
      writer.write(
        s"def is$extName()(using Arena, Context, Block, Recipe): Ref[Bool] = summon[Recipe].$ext\n"
      )
    }

    // ======================================================================================================
    // case class Recipe(val name: String)(using Arena, Context, Block)
    // ======================================================================================================
    writer.write("""
case class Recipe(val name: String)(using Arena, Context, Block) {
  private val indices = scala.collection.mutable.Map[Int, Index]()
""")

    getExtensions().foreach { ext =>
      writer.write(s"  val $ext = smtValue(\"$ext\", Bool)\n")
    }

    writer.write(s"  val allSets: List[Ref[Bool]] = List(${getExtensions().mkString(", ")})\n")

    writer.write("""
  def addIndex(idx: Index): Index = {
    indices.getOrElseUpdate(idx.idx, idx)
  }

  override def toString(): String = {
    val indexStrings = indices.values.map(_.toString).mkString("\n")
    s"Recipe: $name\nIndices:\n$indexStrings"
  }
}

""")

    // ======================================================================================================
    // case class Index(val idx: Int)(using Arena, Context, Block)
    // ======================================================================================================
    writer.write("""
case class Index(val idx: Int)(using Arena, Context, Block) {
  val nameId = smtValue(s"nameId_${idx}", SInt)
""")

    getArgLut().foreach { case (name, arg) =>
      val argName: String = translateToCamelCase(name)
      val argNameLowered = argName.head.toLower + argName.tail
      writer.write(s"  val ${argNameLowered} = smtValue(s\"${name.replace(".", "_")}_$${idx}\", SInt)\n")
    }

    val s = getArgLut().map { case (name, arg) =>
      // CamelCase the argument name
      val argName: String = translateToCamelCase(name)
      val argNameLowered = argName.head.toLower + argName.tail
      s"$$$${${argNameLowered}_$${idx}}"
    }.mkString(", ")

    writer.write(s"""
  override def toString: String = s\"$${idx}, $$$${nameId_$${idx}}, $s\"
}

    """)

    writer.close()
