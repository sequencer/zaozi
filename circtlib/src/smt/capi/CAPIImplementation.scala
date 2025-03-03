// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.smt.capi

import org.llvm.circt.*
import org.llvm.circt.CAPI.*
import org.llvm.mlir.scalalib.{
  given_AttributeApi,
  Attribute,
  Context,
  DialectHandle,
  Identifier,
  LogicalResult,
  Module,
  PassManager,
  Type,
  given
}

import java.lang.foreign.{Arena, MemorySegment}

given DialectHandleApi with
  extension (context: Context)
    inline def loadSmtDialect(
    )(
      using arena: Arena
    ): Unit =
      DialectHandle(mlirGetDialectHandle__smt__(arena)).loadDialect(
        using arena,
        context
      )
end given

// given TypeApi with:
//   inline def getArray(
//     domainType:     Type,
//     rangeType:     Type
//   )(
//     using arena: Arena,
//     context:     Context
//   ): Type
//   inline def getBitVector(
//     width:     Int,
//   )(
//     using arena: Arena,
//     context:     Context
//   ): Type
//   inline def getBool(
//   )(
//     using arena: Arena,
//     context:     Context
//   ): Type
//   inline def getInt(
//   )(
//     using arena: Arena,
//     context:     Context
//   ): Type
//   inline def getSMTFunc(
//     domainTypes:    Seq[Type],
//     rangeType: Type
//   )(
//     using arena: Arena,
//     context:     Context
//   ): Type
//   inline def getSort(
//     identifier:    String,
//     sortParams: Seq[Type]
//   )(
//     using arena: Arena,
//     context:     Context
//   ): Type
//   inline def isArray: Boolean
//   inline def isBitVector: Boolean
//   inline def isBool: Boolean
//   inline def isInt: Boolean
//   inline def isSMTFunc: Boolean
//   inline def isSort: Boolean
// end given

// given AttributeApi with:
//   extension(str: String)
//     inline def getBVCmpPredicateAttribute(
//       using arena: Arena,
//       context:     Context
//     ): Attribute
//     inline def getIntPredicateAttribute(
//       using arena: Arena,
//       context:     Context
//     ): Attribute
//   inline def getBitVectorAttribute(
//     value: BigInt,
//     width: Int
//     )(
//     using arena: Arena,
//     context:     Context
//   ): Attribute

//   inline def isSMTAttribute: Boolean
//   extension(str: String)
//     inline def checkBVCmpPredicateAttribute(
//       using arena: Arena,
//       context:     Context
//     ): Boolean
//     inline def checkIntPredicateAttribute(
//       using arena: Arena,
//       context:     Context
//     ): Boolean
// end given

given ModuleApi with
  extension (module: Module)
    inline def exportSMTLIB(
      callback:    String => Unit
    )(
      using arena: Arena
    ): Unit =
      LogicalResult(
        mlirExportSMTLIB(arena, module.segment, callback.stringToStringCallback.segment, MemorySegment.NULL)
      )
end given