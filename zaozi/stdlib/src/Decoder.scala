// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.stdlib

import mainargs.TokensReader
import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.stdlib.TruthTable.minimize

import java.lang.foreign.Arena

case class DecoderParameter(truthTable: TruthTable) extends Parameter:
  lazy val minimizedTruthTable: TruthTable = minimize(truthTable)

given TokensReader[TruthTable] = new TokensReader.Simple[TruthTable]:
  override def read(strs: Seq[String]): Either[String, TruthTable] = Right(TruthTable(strs.head))
  override def shortName: String = "truth-table"

given upickle.default.ReadWriter[DecoderParameter] = upickle.default.macroRW

class DecoderLayers(parameter: DecoderParameter) extends LayerInterface(parameter)

class DecoderIO(parameter: DecoderParameter) extends HWInterface(parameter):
  val input:  BundleField[Bits] = Flipped(Bits(parameter.truthTable.inputWidth.W))
  val output: BundleField[Bits] = Aligned(Bits(parameter.truthTable.outputWidth.W))

class DecoderProbe(parameter: DecoderParameter) extends DVInterface[DecoderParameter, DecoderLayers](parameter)

@generator
object DecoderModule extends Generator[DecoderParameter, DecoderLayers, DecoderIO, DecoderProbe]:
  def architecture(parameter: DecoderParameter) =
    val io = summon[Interface[DecoderIO]]
    io.output := (
      if (parameter.minimizedTruthTable.table.isEmpty)
         parameter.minimizedTruthTable.default.value.B(parameter.minimizedTruthTable.default.width.W)
      else
        val (inputTerms, outputTerms) = parameter.minimizedTruthTable.table.unzip
        val numberOfInputs            = inputTerms.head.width
        val numberOfOutputs           = outputTerms.head.width
        val inverterMask              = parameter.minimizedTruthTable.default.value
        val invInputs                 = ~io.input
        val andMatrixOutputs          = inputTerms
          .map: t =>
            val andMatrixInput = Seq
              .tabulate(numberOfInputs): i =>
                if (t.mask.testBit(i))
                  Some(
                    if (t.value.testBit(i)) io.input(i)
                    else invInputs(i)
                  )
                else
                  None
              .flatten
            if (andMatrixInput.nonEmpty)
              t.toString -> andMatrixInput.reduce(_ & _)
            else t.toString -> true.B
          .toMap
        val orMatrixOutputs           =
          Seq
            .tabulate(numberOfOutputs): i =>
              val andMatrixLines = parameter.minimizedTruthTable.table
                // OR matrix composed by input terms which makes this output bit a `1`
                .filter { case (_, or) =>
                  or.mask.testBit(i) && or.value.testBit(i)
                }.map { case (inputTerm, _) =>
                  andMatrixOutputs(inputTerm.toString)
                }
              if (andMatrixLines.isEmpty) false.B
              else andMatrixLines.reduce(_ | _)
            .reverse
            .map(_.asBits)
            .reduce(_ ## _)
        val invMatrixOutputs =
          Seq
            .tabulate(numberOfOutputs): i =>
              if (inverterMask.testBit(i))
                !orMatrixOutputs(i)
              else
                orMatrixOutputs(i)
            .reverse
            .map(_.asBits)
            .reduce(_ ## _)
        invMatrixOutputs
      )