// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package org.llvm.circt.scalalib.smt.operation

import org.llvm.mlir.scalalib.{HasOperation, Operation}

class Add(val _operation: Operation)
trait AddApi extends HasOperation[Add]
end AddApi
