// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.stdlib

import mainargs.TokensReader
import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.decoder.*

import java.lang.foreign.Arena

@generator
object PLA extends Generator[DecoderParameter, DecoderLayers, DecoderIO, DecoderProbe]:
  override def moduleName(parameter: DecoderParameter): String =
    "PLA" + "_" + parameter.name + "_" + parameter.hashCode.toHexString
  def architecture(parameter: DecoderParameter) =
    val io                        = summon[Interface[DecoderIO]]
    val (inputTerms, outputTerms) = parameter.pla.table.unzip
    val numberOfInputs            = inputTerms.head.width
    val numberOfOutputs           = outputTerms.head.width
    val inverterMask              = parameter.pla.default.value
    val invInputs                 = ~io.instruction
    val andMatrixOutputs          = inputTerms
      .map: t =>
        val andMatrixInput = Seq
          .tabulate(numberOfInputs): i =>
            if (t.mask.testBit(i))
              Some(
                if (t.value.testBit(i)) io.field[Bits]("instruction")(i)
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
          val andMatrixLines = parameter.pla.table
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
    val invMatrixOutputs          =
      Seq
        .tabulate(numberOfOutputs): i =>
          if (inverterMask.testBit(i))
            !orMatrixOutputs(i)
          else
            orMatrixOutputs(i)
        .reverse
        .map(_.asBits)
        .reduce(_ ## _)
    io.output := invMatrixOutputs.asRecord(new DecoderOutput(parameter.tables))
