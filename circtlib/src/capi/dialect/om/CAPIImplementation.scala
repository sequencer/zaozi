// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Yuhang Zeng <unlsycn@unlsycn.com>
package org.llvm.circt.scalalib.capi.dialect.om

import java.lang.foreign.MemorySegment

given OMEvaluatorApi with
  extension (ref: OMEvaluator)
    inline def segment: MemorySegment = ref._segment
    inline def sizeOf:  Int           = org.llvm.circt.OMEvaluator.sizeof().toInt
end given

given OMEvaluatorValueApi with
  extension (ref: OMEvaluatorValue)
    inline def segment: MemorySegment = ref._segment
    inline def sizeOf:  Int           = org.llvm.circt.OMEvaluatorValue.sizeof().toInt
end given
