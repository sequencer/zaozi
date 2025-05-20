// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.dialect.firrtl

import org.llvm.circt.*
import org.llvm.circt.CAPI.{firrtlImportAnnotationsFromJSONRaw, firrtlValueFoldFlow}
import org.llvm.mlir.scalalib.given
import org.llvm.mlir.scalalib.{given_AttributeApi, Attribute, AttributeApi as MlirAttributeApi, Context, Value}

import java.lang.foreign.Arena

given UtilityApi with
  inline def importAnnotationsFromJSONRaw(
    annotationsStr: String
  )(
    using arena:    Arena,
    context:        Context
  ): Attribute =
    val attribute = summon[MlirAttributeApi].allocateAttribute
    firrtlImportAnnotationsFromJSONRaw(
      context.segment,
      annotationsStr.toStringRef.segment,
      attribute.segment
    )
    attribute
  inline def valueFoldFlow(value: Value, flow: FirrtlValueFlow): FirrtlValueFlow =
    firrtlValueFoldFlow(value.segment, flow.toNative).fromNative
end given
