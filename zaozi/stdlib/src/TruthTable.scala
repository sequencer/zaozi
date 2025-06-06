// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.stdlib

private def groupByIntoSeq[A, K](xs: Iterable[A])(f: A => K): Seq[(K, Seq[A])] =
  val map = scala.collection.mutable.LinkedHashMap.empty[K, scala.collection.mutable.ListBuffer[A]]
  for (x <- xs)
    val key = f(x)
    val l   = map.getOrElseUpdate(key, scala.collection.mutable.ListBuffer.empty[A])
    l += x
  map.view
    .map:
      case (k, vs) => k -> vs.toList
    .toList

case class TruthTable(table: Seq[(BitPat, BitPat)], default: BitPat):
  def inputWidth:  Int = table.head._1.width
  def outputWidth: Int = table.head._2.width

  override def toString: String =
    def writeRow(map: (BitPat, BitPat)): String =
      s"${map._1.toString}->${map._2.toString}"
    (table.map(writeRow) ++ Seq(s"${" " * (inputWidth + 2)}${default.toString}")).mkString(";")

  def copy(table: Seq[(BitPat, BitPat)] = this.table, default: BitPat = this.default): TruthTable =
    TruthTable(table, default)

  override def equals(y: Any): Boolean =
    y match
      case that: TruthTable => this.table == that.table && this.default == that.default
      case _ => false

  override lazy val hashCode: Int = scala.util.hashing.MurmurHash3.productHash((table, default))

given upickle.default.ReadWriter[TruthTable] = upickle.default
  .readwriter[String]
  .bimap[TruthTable](
    tb => tb.toString,
    str => TruthTable(str)
  )

object TruthTable:
  /** Public apply method to TruthTable. Calls apply_impl with the default value true of checkCollisions */
  def apply(table: Iterable[(BitPat, BitPat)], default: BitPat): TruthTable =
    apply_impl(table, default, true)

  /** Parse TruthTable from its string representation. */
  def apply(tableString: String): TruthTable =
    TruthTable(
      tableString
        .split(";")
        .filter(_.contains("->"))
        .map(_.split("->").map(str => BitSet.bitpat(str)))
        .map(bps => bps(0) -> bps(1))
        .toSeq,
      BitSet.bitpat(s"${tableString.split(";").filterNot(_.contains("->")).head.replace(" ", "")}")
    )

  def minimize(table: TruthTable): TruthTable =
    TruthTable.merge(
      TruthTable
        .split(table)
        .map:
          case (table, indexes) => (espresso(table), indexes)
    )

  /** Pad the input signals to equalize all input widths. Pads input signals to the maximum width found in the table.
    *
    * @param table
    *   the truth table whose rows will be padded
    * @return
    *   the same truth table but with inputs padded
    */
  private def padInputs(table: Iterable[(BitPat, BitPat)]): Iterable[(BitPat, BitPat)] =
    val inputWidth = table.map(_._1.width).max
    table.map:
      case (in, out) if inputWidth > in.width =>
        (BitSet.N(inputWidth - in.width) ## in, out)
      case (in, out)                          => (in, out)

  /** For each duplicated input, collect the outputs into a single Seq.
    *
    * @param table
    *   the truth table
    * @return
    *   a Seq of tuple of length 2, where the first element is the input and the second element is a Seq of OR-ed
    *   outputs for the input
    */
  private def mergeTableOnInputs(table: Iterable[(BitPat, BitPat)]): Seq[(BitPat, Seq[BitPat])] =
    groupByIntoSeq(table)(_._1).map:
      case (input, mappings) => input -> mappings.map(_._2)

  /** Merge two BitPats by OR-ing the values and masks, and setting the width to the max width among the two
    */
  private def merge(a: BitPat, b: BitPat): BitPat =
    BitSet.bitpat(a.value | b.value, a.mask | b.mask, a.width.max(b.width))

  /** Call Espresso to minimize the TruthTable. */
  private def espresso(table: TruthTable): TruthTable =
    def writeTable(table: TruthTable): String =
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
      val rawTable = table.toString
        .split(";")
        .filter(_.contains("->"))
        .mkString("\n")
        .replace("->", " ")
        .replace('?', '-')
      // invert all output, since espresso cannot handle default is on.
      val invertRawTable = rawTable
        .split(";")
        .map(_.split(" "))
        .map(row => s"${row(0)} ${invert(row(1))}")
        .mkString("\n")
      s""".i ${table.inputWidth}
         |.o ${table.outputWidth}
         |.type $tableType
         |""".stripMargin ++ (if (defaultType == '1') invertRawTable else rawTable)

    def readTable(espressoTable: String) = {
      def bitPat(espresso: String): BitPat = BitSet.bitpat(espresso.replace('-', '?'))

      val out = espressoTable
        .split("\n")
        .filterNot(_.startsWith("."))
        .map(_.split(' '))
        .map(row => bitPat(row(0)) -> bitPat(row(1)))
      // special case for 0 and DontCare, if output is not couple to input
      if (out.isEmpty)
        Array(
          (
            BitSet.bitpat("?" * table.inputWidth),
            BitSet.bitpat("0" * table.outputWidth)
          )
        )
      else out
    }

    val input  = writeTable(table)
    val output =
      try
        // TODO: CIRCT should provide this API eventually.
        os.proc("espresso").call(stdin = input).out.chunks.mkString
      catch
        case e: java.io.IOException if e.getMessage.contains("error=2, No such file or directory") =>
          throw new Exception("espresso not found.")
    TruthTable.fromEspressoOutput(readTable(output), table.default)

  /** Public method for calling with the Espresso decoder format fd
    *
    * For Espresso, for each output, a 1 means this product term belongs to the ON-set, a 0 means this product term has
    * no meaning for the value of this function. This is the same as the fd (or f) type in espresso.
    *
    * @param table
    *   the truth table
    * @param default
    *   the default BitPat is made up of a single bit type, either "?", "0" or "1". A default of "?" sets Espresso to
    *   fr-format, while a "0" or "1" sets it to the fd-format.
    * @return
    *   a fully built TruthTable
    */
  private def fromEspressoOutput(table: Iterable[(BitPat, BitPat)], default: BitPat): TruthTable =
    apply_impl(table, default, false)

  /** Convert a table and default output into a [[TruthTable]]. */
  private def apply_impl(
    table:           Iterable[(BitPat, BitPat)],
    default:         BitPat,
    checkCollisions: Boolean
  ): TruthTable =
    val paddedTable = padInputs(table)

    require(table.map(_._2.width).toSet.size == 1, "output width not equal.")

    val mergedTable = mergeTableOnInputs(paddedTable)

    val finalTable: Seq[(BitPat, BitPat)] = mergedTable.map:
      case (input, outputs) =>
        val (result, noCollisions) = outputs.tail.foldLeft((outputs.head, checkCollisions)):
          case ((acc, ok), o) => (merge(acc, o), ok && acc.overlap(o))
        // Throw an error if checkCollisions is true but there are bits with a non-zero overlap.
        require(!checkCollisions || noCollisions, s"TruthTable conflict on merged row:\n  $input -> $outputs")
        (input, result)
    new TruthTable(finalTable.sorted, default)

  /** consume 1 table, split it into up to 3 tables with the same default bits.
    *
    * @return
    *   table and its indexes from original bits.
    * @note
    *   Since most of minimizer(like espresso) cannot handle a multiple default table. It is useful to split a table
    *   into 3 tables based on the default type.
    */
  private def split(
    table: TruthTable
  ): Seq[(TruthTable, Seq[Int])] =
    def bpFilter(bitPat: BitPat, indexes: Seq[Int]): BitPat =
      BitSet.bitpat(bitPat.toString.zipWithIndex.filter(b => indexes.contains(b._2)).map(_._1).mkString)

    def tableFilter(indexes: Seq[Int]): Option[(TruthTable, Seq[Int])] =
      if (indexes.nonEmpty)
        Some(
          (
            TruthTable(
              table.table.map:
                case (in, out) => in -> bpFilter(out, indexes)
              ,
              bpFilter(table.default, indexes)
            ),
            indexes
          )
        )
      else None

    def index(bitPat: BitPat, bpType: Char): Seq[Int] =
      bitPat.toString.zipWithIndex.filter(_._1 == bpType).map(_._2)

    // We need to split if the default has a mix of values (no need to split if all ones, all zeros, or all ?)
    val needToSplit = !(table.default.allDontCares || table.default.allZeros || table.default.allOnes)
    if (needToSplit)
      Seq('1', '0', '?').flatMap(t => tableFilter(index(table.default, t)))
    else
      Seq(table -> (0 until table.default.width))

  /** consume tables, merge it into single table with different default bits.
    *
    * @note
    *   Since most of minimizer(like espresso) cannot handle a multiple default table. It is useful to split a table
    *   into 3 tables based on the default type.
    */
  private def merge(
    tables: Seq[(TruthTable, Seq[Int])]
  ): TruthTable =
    def reIndex(bitPat: BitPat, table: TruthTable, indexes: Seq[Int]): Seq[(Char, Int)] =
      table.table
        .map(a => a._1.toString -> a._2)
        .collectFirst:
          case (k, v) if k == bitPat.toString => v
        .getOrElse(BitSet.DC(indexes.size))
        .toString
        .zip(indexes)
    def bitPat(indexedChar: Seq[(Char, Int)]) = BitSet.bitpat(s"${indexedChar.sortBy(_._2).map(_._1).mkString}")
    val needToMerge = tables.size > 1
    if (needToMerge)
      TruthTable(
        tables
          .flatMap(_._1.table.map(_._1))
          .map: key =>
            key -> bitPat(tables.flatMap:
              case (table, indexes) => reIndex(key, table, indexes)
            ),
        bitPat(tables.flatMap:
          case (table, indexes) => table.default.toString.zip(indexes)
        )
      )
    else
      tables.head._1
