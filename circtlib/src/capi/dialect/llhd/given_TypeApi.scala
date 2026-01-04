// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.capi.dialect.llhd

import org.llvm.circt.CAPI.llhdTypeIsATimeType
import org.llvm.mlir.scalalib.capi.ir.{Type, given}

import java.lang.foreign.Arena

given TypeApi with
  extension (tpe: Type) inline def isTimeType: Boolean = llhdTypeIsATimeType(tpe.segment)
end given
