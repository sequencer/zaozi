// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.valuetpe

import me.jiuyang.zaozi.{Layer, TypeImpl}
import org.llvm.mlir.scalalib.{Context, Type}

import java.lang.foreign.Arena

trait CanProbe

// UInt is a Data type, Probe[UInt] is either a Data,
// But it cannot be a UInt to avoid the UInt extension exposing to it.
trait RProbe[T <: CanProbe & Data] extends Data:
  private[zaozi] val _baseType: T
  private[zaozi] val _color:    Layer

  final def toMlirType(
    using Arena,
    Context,
    TypeImpl
  ): Type = this.toMlirTypeImpl

trait RWProbe[T <: CanProbe & Data] extends Data:
  private[zaozi] val _baseType: T
  private[zaozi] val _color:    Layer

  final def toMlirType(
    using Arena,
    Context,
    TypeImpl
  ): Type = this.toMlirTypeImpl
