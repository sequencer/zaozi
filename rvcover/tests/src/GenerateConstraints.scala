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

    getArgLut().foreach { case (name, arg) =>
      // camelCase the argument name
      val argName: String = translateToCamelCase(name)
      val argNameLowered = argName.head.toLower + argName.tail

      writer.write(
        s"def ${argNameLowered}Range(start: Int, end: Int)(using Arena, Context, Block, Index): Unit = smtAssert(summon[Index].${argNameLowered} >= start.S & summon[Index].${argNameLowered} < end.S)\n"
      )
    }

    writer.write("\n\n")

    getArgLut().foreach { case (name, arg) =>
      // camelCase the argument name
      val argName: String = translateToCamelCase(name)
      val argNameLowered = argName.head.toLower + argName.tail
      writer.write(
        s"def has${argName}()(using Arena, Context, Block, Index): Unit = ${argNameLowered}Range(0, ${1 << (arg.msb - arg.lsb + 1)})\n"
      )
    }

    writer.write("\n\n")

    writer.write(
      "def nameId(idx: Int)(using Arena, Context, Block, Index): Unit = smtAssert(summon[Index].nameId === idx.S)\n"
    )

    getInstructions().zipWithIndex.foreach { case (instruction, idx) =>
      // CamelCase the instruction name
      val name = translateToCamelCase(instruction.name)

      var s = s"def is$name()(using Arena, Context, Block, Index): Unit = \n  nameId($idx)\n"
      instruction.args.foreach { arg =>
        // CamelCase the argument name
        val argName = translateToCamelCase(arg.name)
        s = s + s"  has$argName()\n"
      }

      writer.write(s + "\n")
    }

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
