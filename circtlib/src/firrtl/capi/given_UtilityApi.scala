// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.firrtl.capi

import org.llvm.circt.*
import org.llvm.circt.CAPI.{mlirGetDialectHandle__firrtl__ as _, *}
import org.llvm.mlir.scalalib.given
import org.llvm.mlir.scalalib.{given_AttributeApi, Attribute, Context, Value}

import java.lang.foreign.Arena

given UtilityApi with
  inline def importAnnotationsFromJSONRaw(
    annotationsStr: String
  )(
    using arena:    Arena,
    context:        Context
  ): Attribute =
    val attribute = summon[org.llvm.mlir.scalalib.AttributeApi].allocateAttribute
    firrtlImportAnnotationsFromJSONRaw(
      context.segment,
      annotationsStr.toStringRef.segment,
      attribute.segment
    )
    attribute
  inline def valueFoldFlow(value: Value, flow: FirrtlValueFlow): FirrtlValueFlow =
    firrtlValueFoldFlow(value.segment, flow.toNative).fromNative
end given
