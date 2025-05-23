// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.integerset

import org.llvm.mlir.scalalib.capi.support.{*, given}

import java.lang.foreign.{Arena, MemorySegment}

class IntegerSet(val _segment: MemorySegment)
trait IntegerSetApi extends HasSegment[IntegerSet] with HasSizeOf[IntegerSet]
