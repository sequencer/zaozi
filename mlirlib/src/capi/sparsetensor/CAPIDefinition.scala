// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.sparsetensor

import org.llvm.mlir.scalalib.capi.support.{*, given}

import java.lang.foreign.{Arena, MemorySegment}

class SparseTensorLevelType(val _segment: MemorySegment)
trait SparseTensorLevelTypeApi extends HasSegment[SparseTensorLevelType]
