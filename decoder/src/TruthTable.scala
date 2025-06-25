// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.decoder

import upickle.default.ReadWriter

import scala.collection.immutable.SortedMap

object TruthTable:
  def apply(str: String): TruthTable =
    str match
      case s"[$name][$default][$encodingStr][$pairStr]" =>
        TruthTable(
          name,
          pairStr
            .split(',')
            .map: entry =>
              val Array(bitsetStr, valueStr) = entry.split(":").map(_.trim)
              BitSet.bitset(bitsetStr) -> valueStr
            .toSeq,
          default,
          SortedMap.from(
            encodingStr
              .split(',')
              .map: entry =>
                val Array(key, value) = entry.split(':').map(_.trim)
                key -> BitSet.bitpat(value)
          )
        )
      case _                                            =>
        throw new IllegalArgumentException(s"Invalid TruthTable format: $str")

case class TruthTable(name: String, pair: Seq[(BitSet, String)], default: String, encoding: SortedMap[String, BitPat]):
  override def toString: String =
    s"[${name}]" +
      "[" + default + "]" +
      "[" + encoding.map((k, v) => s"$k:$v").mkString(",") + "]" +
      "[" + pair.map((bitSet, value) => s"${bitSet.toString}:$value").mkString(",") + "]"

  def inputBits:  Int                   = pair.head._1.width
  def outputBits: Int                   = encoding(default).width
  def input:      Seq[BitSet]           = pair.map(_._1)
  def output:     Seq[BitSet]           = pair.map(p => encoding(p._2))
  def table:      Seq[(BitPat, BitPat)] = pair.zipWithIndex.flatMap:
    case ((input, value), idx) =>
      input.terms.map: bp =>
        bp -> encoding(pair(idx)._2)
  require(pair.nonEmpty, "TruthTable must have at least one entry")
  require(pair.forall(_._1.width == pair.head._1.width), "All bit sets must have the same width")
  (pair.map(_._2) :+ default).foreach(i =>
    require(
      encoding.keys.toSet.contains(i),
      s"Unknown encoding: ${i}, available encodings: ${encoding.keys.mkString(";")}"
    )
  )
  encoding.foreach(i =>
    require(
      i._2.width == encoding.head._2.width,
      s"All bit patterns must have the same width: ${encoding.head._2.width}: ${i._1}: ${i._2}"
    )
  )
  encoding.foreach(e =>
    require(!e._2.hasDontCares || e._2.allDontCares, s"Encoding cannot be partially defined: ${e._1}->${e._2}")
  )
  pair
    .map(_._1)
    .zipWithIndex
    .foreach:
      case (l, i) =>
        pair
          .map(_._1)
          .zipWithIndex
          .foreach:
            case (r, j) =>
              if (i > j)
                require(!l.overlap(r), "TruthTable entries " + l + " and " + r + " overlap")

given upickle.default.ReadWriter[TruthTable] =
  upickle.default.readwriter[String].bimap[TruthTable](_.toString, TruthTable.apply)
