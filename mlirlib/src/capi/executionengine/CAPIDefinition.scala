// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.executionengine

import org.llvm.mlir.scalalib.capi.support.{*, given}

import java.lang.foreign.{Arena, MemorySegment}

class ExecutionEngine(val _segment: MemorySegment)
trait ExecutionEngineApi extends HasSegment[ExecutionEngine] with HasSizeOf[ExecutionEngine]
