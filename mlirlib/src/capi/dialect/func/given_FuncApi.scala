// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package org.llvm.mlir.scalalib.capi.dialect.func

import org.llvm.mlir.scalalib.capi.ir.{
  Block,
  Context,
  LocationApi,
  Module,
  NamedAttributeApi,
  Operation,
  OperationApi,
  given
}

import java.lang.foreign.Arena

// Structure
given FuncApi with
  inline def op(
    symName:     String
    // funcType: Type,
    // symVisibility: String,
    // argAttrs: Seq[NamedAttribute],
    // resAttrs: Seq[NamedAttribute],
    // noInline: Boolean,
  )(
    using arena: Arena,
    context:     Context
  ): Func = Func(
    summon[OperationApi].operationCreate(
      name = "func.func",
      location = summon[LocationApi].locationUnknownGet,
      regionBlockTypeLocations = Seq(
        Seq(
          (Seq.empty, Seq.empty)
        )
      ),
      namedAttributes =
        val namedAttributeApi = summon[NamedAttributeApi]
        // val noInlineAttr = noInline match
        //   case true =>
        //     Seq(
        //       // ::mlir::UnitAttr
        //       namedAttributeApi.namedAttributeGet("noInline".identifierGet, summon[AttributeApi].unitAttrGet)
        //     )
        //   case false => Seq.empty
        Seq(
          // ::mlir::StringAttr
          namedAttributeApi.namedAttributeGet("symName".identifierGet, symName.stringAttrGet)
          // ::mlir::TypeAttr
          // namedAttributeApi.namedAttributeGet("funcType".identifierGet, ???),
          // ::mlir::StringAttr
          // namedAttributeApi.namedAttributeGet("symVisibility".identifierGet, ???),
          // ::mlir::ArrayAttr
          // namedAttributeApi.namedAttributeGet("argAttrs".identifierGet, ???),
          // ::mlir::ArrayAttr
          // namedAttributeApi.namedAttributeGet("resAttrs".identifierGet, ???),
        )
        // ++ noInlineAttr
    )
  )
  extension (c:   Func)
    inline def block(
      using Arena
    ): Block = c.operation.getFirstRegion.getFirstBlock
    inline def appendToModule(
    )(
      using arena: Arena,
      module:      Module
    ): Unit =
      module.getBody.appendOwnedOperation(c.operation)
  extension (ref: Func) def operation: Operation = ref._operation
end given
