// // SPDX-License-Identifier: Apache-2.0
// // SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
// package me.jiuyang.rvcover.util

// sealed class BitPat(val value: BigInt, val mask: BigInt, val width: Int) {

//   /** Get specified width of said BitPat
//     */
//   def getWidth: Int = width

//   def equals(that: BitPat): Boolean =
//     this.value == that.value && this.mask == that.mask && this.width == that.width

//   protected def _applyImpl(
//     x:                   Int
//   )(
//     implicit sourceInfo: SourceInfo
//   ): BitPat = {
//     _applyImpl(x, x)
//   }

//   protected def _applyImpl(
//     x:                   Int,
//     y:                   Int
//   )(
//     implicit sourceInfo: SourceInfo
//   ): BitPat = {
//     require(width > x && y >= 0, s"Invalid bit range ($x, $y), index should be bounded by (${width - 1}, 0)")
//     require(x >= y, s"Invalid bit range ($x, $y), x should be greater or equal to y.")
//     BitPat(s"b${rawString.slice(width - x - 1, width - y)}")
//   }

//   protected def _impl_===(
//     that:                UInt
//   )(
//     implicit sourceInfo: SourceInfo
//   ): Bool = {
//     value.asUInt === (that & mask.asUInt)
//   }

//   protected def _impl_=/=(
//     that:                UInt
//   )(
//     implicit sourceInfo: SourceInfo
//   ): Bool = {
//     !(this._impl_===(that))
//   }

//   protected def _impl_##(
//     that:                BitPat
//   )(
//     implicit sourceInfo: SourceInfo
//   ): BitPat = {
//     new BitPat((value << that.getWidth) + that.value, (mask << that.getWidth) + that.mask, this.width + that.getWidth)
//   }

//   /** Check whether this `BitPat` overlap with that `BitPat`, i.e. !(intersect.isEmpty)
//     *
//     * @param that
//     *   `BitPat` to be checked.
//     * @return
//     *   true if this and that `BitPat` have overlap.
//     */
//   override def overlap(that: BitPat): Boolean =
//     ((mask & that.mask) & (value ^ that.value)) == 0

//   /** Generate raw string of a `BitPat`. */
//   def rawString: String = _rawString

//   // This is micro-optimized and memoized because it is used for lots of BitPat operations
//   private lazy val _rawString: String = {
//     val sb = new StringBuilder(width)
//     var i  = 0
//     while (i < width) {
//       val bitIdx = width - i - 1
//       val char   =
//         if (mask.testBit(bitIdx)) {
//           if (value.testBit(bitIdx)) {
//             '1'
//           } else {
//             '0'
//           }
//         } else {
//           '?'
//         }
//       sb += char
//       i += 1
//     }
//     sb.result()
//   }

//   override def toString = s"BitPat($rawString)"
// }

// /** Special case when output type is a single Bool
//   *
//   * @tparam T
//   *   pattern this field should match
//   */
// trait BoolDecodeField[T <: DecodePattern] extends DecodeField[T, Bool] {
//   def chiselType: Bool = Bool()

//   def y: BitPat = BitPat.Y(1)

//   def n: BitPat = BitPat.N(1)
// }

// /** One output field of a decoder bundle
//   *
//   * @tparam T
//   *   pattern this field should match
//   * @tparam D
//   *   output type of this field
//   */
// trait DecodeField[T <: DecodePattern, D <: Data] {
//   def name: String

//   def chiselType: D

//   def default: BitPat = dc

//   final def width: Int = chiselType.getWidth

//   def dc: BitPat = BitPat.dontCare(width)

//   def genTable(op: T): BitPat

//   require(width == default.width)
// }

// /** Input pattern a DecoderField should match, e.g. an instruction
//   */
// trait DecodePattern {
//   def bitPat: BitPat
// }

// /** A structured way of generating large decode tables, often found in CPU instruction decoders
//   *
//   * Each field is a `DecoderPattern`, its genTable method will be called for each possible pattern and gives expected
//   * output for this field as a `BitPat`.
//   *
//   * @param patterns
//   *   all possible input patterns, should implement trait DecoderPattern
//   * @param fields
//   *   all fields as decoded output
//   * @tparam I
//   *   concrete type of input patterns trait
//   */
// class DecodeTable[I <: DecodePattern](patterns: Seq[I], fields: Seq[DecodeField[I, ? <: Data]]) {
//   require(patterns.map(_.bitPat.getWidth).distinct.size == 1, "All instructions must have the same width")

//   def bundle: DecodeBundle = new DecodeBundle(fields)

//   lazy val table: TruthTable = TruthTable(
//     patterns.map { op => op.bitPat -> fields.reverse.map(field => field.genTable(op)).reduce(_ ## _) },
//     fields.reverse.map(_.default).reduce(_ ## _)
//   )

//   def decode(input: UInt): DecodeBundle = chisel3.util.experimental.decode.decoder(input, table).asTypeOf(bundle)
// }
