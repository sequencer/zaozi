// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.decoder

object PLA:
  def apply(str: String): PLA =
    str match
      case s"[$default][$tableStr]" =>
        PLA(
          tableStr
            .split(",")
            .map { part =>
              val Array(input, output) = part.split(":").map(_.trim)
              (BitSet.bitpat(input), BitSet.bitpat(output))
            }
            .toSeq,
          BitSet.bitpat(default)
        )
      case _                        =>
        throw new IllegalArgumentException(s"Invalid PLA format: $str")

case class PLA(table: Seq[(BitPat, BitPat)], default: BitPat):
  def inputWidth:        Int    = table.head._1.width
  def outputWidth:       Int    = table.head._2.width
  table.map(_._1).foreach(bp => require(bp.width == inputWidth, "input width not match"))
  (table.map(_._2) :+ default).foreach(bp => require(bp.width == outputWidth, "output width not match"))
  override def toString: String = s"[$default][" + table.map((k, v) => s"$k:$v").mkString(",") + "]"

given upickle.default.ReadWriter[PLA] = upickle.default.readwriter[String].bimap[PLA](_.toString, PLA.apply)
