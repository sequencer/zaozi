// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.affineexpr

import org.llvm.mlir.scalalib.capi.support.{*, given}

import java.lang.foreign.MemorySegment

class AffineExpr(val _segment: MemorySegment)
trait AffineExprApi extends HasSegment[AffineExpr] with HasSizeOf[AffineExpr]
