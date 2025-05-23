// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.affinemap

import org.llvm.mlir.scalalib.capi.support.{*, given}

import java.lang.foreign.MemorySegment

class AffineMap(val _segment: MemorySegment)
trait AffineMapApi extends HasSegment[AffineMap] with HasSizeOf[AffineMap]
