// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.mlir.scalalib.capi.rewrite

import org.llvm.mlir.scalalib.capi.support.{*, given}

import java.lang.foreign.{Arena, MemorySegment}

class FrozenRewritePatternSet(val _segment: MemorySegment)
trait FrozenRewritePatternSetApi extends HasSegment[FrozenRewritePatternSet] with HasSizeOf[FrozenRewritePatternSet]

class GreedyRewriteDriverConfig(val _segment: MemorySegment)
trait GreedyRewriteDriverConfigApi
    extends HasSegment[GreedyRewriteDriverConfig]
    with HasSizeOf[GreedyRewriteDriverConfig]

class PDLPatternModule(val _segment: MemorySegment)
trait PDLPatternModuleApi extends HasSegment[PDLPatternModule] with HasSizeOf[PDLPatternModule]

class RewritePatternSet(val _segment: MemorySegment)
trait RewritePatternSetApi extends HasSegment[RewritePatternSet] with HasSizeOf[RewritePatternSet]

class RewriterBase(val _segment: MemorySegment)
trait RewriterBaseApi extends HasSegment[RewriterBase] with HasSizeOf[RewriterBase]
