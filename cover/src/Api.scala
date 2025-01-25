// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>

package cover

trait Instruction {
  def name: String
  def attributes: Map[String, Any]
}

trait Constraint {
  def apply(attributes: Map[String, Any]): Boolean
}

trait InstructionGenerator {
  def instruction(name: String, count: Int): Unit

  def constraint(constraint: Constraint): Unit

  def build(): Seq[Instruction]

  def clear(): Unit
}