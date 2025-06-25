// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.decoder

def espresso(tables: Seq[TruthTable]): PLA =
  require(tables.nonEmpty, "espresso doesn't accept empty table")
  def minimize(table: PLA): PLA =
    def bitPatToEspresso(bitPat: BitPat): String                = bitPat.toString.replace('?', '-')
    def writeTable(table: PLA):           String                =
      def invert(string: String) = string
        .replace('0', 't')
        .replace('1', '0')
        .replace('t', '1')
      val defaultType: Char   =
        val t = table.default.toString.toCharArray.distinct
        require(t.length == 1, "Internal Error: espresso only accept unified default type.")
        t.head
      val tableType:   String = defaultType match
        case '?' => "fr"
        case _   => "fd"
      val rawTable = table.table.map((i, o) => s"${bitPatToEspresso(i)} ${bitPatToEspresso(o)}").mkString("\n")
      // invert all output, since espresso cannot handle default is on.
      // TODO: we may use the .phase for it, however the behavior of 0, phase, - are misleading....
      val invertRawTable =
        table.table.map((i, o) => s"${bitPatToEspresso(i)} ${invert(bitPatToEspresso(o))}").mkString("\n")
      s""".i ${table.inputWidth}
         |.o ${table.outputWidth}
         |.type $tableType
         |""".stripMargin ++ (if (defaultType == '1') invertRawTable else rawTable)
    def readTable(espressoTable: String): Seq[(BitPat, BitPat)] =
      def bitPat(str: String): BitPat =
        BitSet.bitpat(str.replace('-', '?'))
      val out = espressoTable
        .split("\n")
        .filterNot(_.startsWith("."))
        .map(_.split(' '))
        .map(row => bitPat(row(0)) -> bitPat(row(1)))
      // special case for 0 and DontCare, if output is not couple to input
      if (out.isEmpty)
        Array(
          (
            BitSet.all(table.inputWidth),
            BitSet.n(table.outputWidth)
          )
        )
      else out
    PLA(readTable(os.proc("espresso").call(stdin = writeTable(table)).out.chunks.mkString), table.default)
  def split(
    table: PLA
  ): Seq[(PLA, Seq[Int])] =
    def bpFilter(bitPat: BitPat, indexes: Seq[Int]): BitPat                  =
      BitSet.bitpat(s"${bitPat.toString.zipWithIndex.filter(b => indexes.contains(b._2)).map(_._1).mkString}")
    def tableFilter(indexes: Seq[Int]):              Option[(PLA, Seq[Int])] =
      if (indexes.nonEmpty)
        Some(
          (
            PLA(
              table.table.map { case (in, out) => in -> bpFilter(out, indexes) },
              bpFilter(table.default, indexes)
            ),
            indexes
          )
        )
      else None
    def index(bitPat: BitPat, bpType: Char):         Seq[Int]                =
      bitPat.toString.zipWithIndex.filter(_._1 == bpType).map(_._2)
    // We need to split if the default has a mix of values (no need to split if all ones, all zeros, or all ?)
    val needToSplit = !(table.default.allDontCares || table.default.allZeros || table.default.allOnes)
    if (needToSplit) Seq('1', '0', '?').flatMap(t => tableFilter(index(table.default, t)))
    else Seq(table -> (0 until table.default.width))
  def merge(
    tables: Seq[(PLA, Seq[Int])]
  ): PLA =
    def reIndex(bitPat: BitPat, table: PLA, indexes: Seq[Int]): Seq[(Char, Int)] =
      table.table
        .map(a => a._1.toString -> a._2)
        .collectFirst:
          case (k, v) if k == bitPat.toString => v
        .getOrElse(BitSet.all(indexes.size))
        .toString
        .zip(indexes)
    def bitPat(indexedChar: Seq[(Char, Int)]) = BitSet.bitpat(s"${indexedChar
        .sortBy(_._2)
        .map(_._1)
        .mkString}")
    if (tables.size > 1)
      PLA(
        tables
          .flatMap(_._1.table.map(_._1))
          .map: key =>
            key -> bitPat(tables.flatMap { case (table, indexes) => reIndex(key, table, indexes) }),
        bitPat(tables.flatMap { case (table, indexes) => table.default.toString.zip(indexes) })
      )
    else tables.head._1
  merge(
    split(
      PLA(
        tables
          .flatMap(_.table.map(_._1))
          .distinct
          .map: input =>
            (
              input,
              tables.map(t => t.table.find(_._1 == input).map(_._2).getOrElse(t.encoding(t.default))).reduce(_ ## _)
            ),
        tables.map(t => t.encoding(t.default)).reduce(_ ## _)
      )
    ).map { case (table, indexes) => (minimize(table), indexes) }
  )
