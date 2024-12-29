// SPDX-License-Identifier: Apache-2.0
package org.llvm.mlir.scalalib

import org.llvm.mlir.*
import org.llvm.mlir.CAPI.*

import java.lang.foreign.MemorySegment

given DiagnosticHandlerApi with
  extension (diagnosticHandler: DiagnosticHandler)
    inline def segment: MemorySegment = diagnosticHandler._segment
end given

given DiagnosticHandlerIDApi with
  extension (diagnosticHandlerID: DiagnosticHandlerID)
    inline def segment: MemorySegment = diagnosticHandlerID._segment
end given

given DiagnosticEnumApi with
  extension (int: Int)
    inline def fromNative: DiagnosticSeverityEnum = int match
      case i if i == MlirDiagnosticError()   => DiagnosticSeverityEnum.Error
      case i if i == MlirDiagnosticNote()    => DiagnosticSeverityEnum.Note
      case i if i == MlirDiagnosticRemark()  => DiagnosticSeverityEnum.Remark
      case i if i == MlirDiagnosticWarning() => DiagnosticSeverityEnum.Warning
  extension (ref: DiagnosticSeverityEnum)
    inline def toNative: Int = ref match
      case DiagnosticSeverityEnum.Error   => MlirDiagnosticError()
      case DiagnosticSeverityEnum.Note    => MlirDiagnosticNote()
      case DiagnosticSeverityEnum.Remark  => MlirDiagnosticRemark()
      case DiagnosticSeverityEnum.Warning => MlirDiagnosticWarning()
    inline def sizeOf:   Int = 4
end given

