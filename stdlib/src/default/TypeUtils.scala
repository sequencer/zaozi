// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Yuhang Zeng <unlsycn@unlsycn.com>
package me.jiuyang.stdlib.default

import me.jiuyang.stdlib.*
import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

import java.lang.foreign.Arena

given TypeUtilsApi with
  extension [D <: HardwareDataType](ref: Referable[D])
    inline def asBits(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[Bits] = ref.getType match
      case _: Bool   => given_BoolApi_R.asBits(ref.asInstanceOf[Referable[Bool]])
      case _: Bundle => given_BundleApi_T_R.asBits(ref.asInstanceOf[Referable[Bundle]])
      case _: Record => given_RecordApi_T_R.asBits(ref.asInstanceOf[Referable[Record]])
      case _: SInt   => given_SIntApi_R.asBits(ref.asInstanceOf[Referable[SInt]])
      case _: UInt   => given_UIntApi_R.asBits(ref.asInstanceOf[Referable[UInt]])
      case _: Vec[?] =>
        given_VecApi_E_V_R.asBits(
          // we don't care about the type parameter of Vec here
          ref.asInstanceOf[Referable[Vec[Bool]]]
        )

  extension (ref: Referable[Bits])
    inline def asTypeOf[D <: HardwareDataType, R <: Referable[D]](
      that: R
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Node[D] = that.getType match
      case _: Bool   => ref.asBool.asInstanceOf[Node[D]]
      case x: Bundle => ref.asBundle[Bundle](x).asInstanceOf[Node[D]]
      case x: Record => ref.asRecord[Record](x).asInstanceOf[Node[D]]
      case _: SInt   => ref.asSInt.asInstanceOf[Node[D]]
      case _: UInt   => ref.asUInt.asInstanceOf[Node[D]]
      case x: Vec[?] => ref.asVec(x.getElementType).asInstanceOf[Node[D]]

end given
