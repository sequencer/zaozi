// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.dialect.firrtl.operation

import org.llvm.mlir.scalalib.capi.support.HasOperation
import org.llvm.mlir.scalalib.capi.ir.Operation

class Assert(val _operation: Operation)
class Assume(val _operation: Operation)
class Attach(val _operation: Operation)
class Connect(val _operation: Operation)
trait ConnectApi extends HasOperation[Connect]:
end ConnectApi

class Cover(val _operation: Operation)
class Force(val _operation: Operation)
class LayerBlock(val _operation: Operation)
trait LayerBlockApi        extends HasOperation[LayerBlock]:
end LayerBlockApi
class Match(val _operation: Operation)
class MatchingConnect(val _operation: Operation)
class Printf(val _operation: Operation)
class Propassign(val _operation: Operation)
class RefDefine(val _operation: Operation)
trait RefDefineApi         extends HasOperation[RefDefine]:
end RefDefineApi
class RefForceInitial(val _operation: Operation)
trait RefForceInitialApi   extends HasOperation[RefForceInitial]:
end RefForceInitialApi
class RefForce(val _operation: Operation)
trait RefForceApi          extends HasOperation[RefForce]:
end RefForceApi
class RefReleaseInitial(val _operation: Operation)
trait RefReleaseInitialApi extends HasOperation[RefReleaseInitial]:
end RefReleaseInitialApi
class RefRelease(val _operation: Operation)
trait RefReleaseApi        extends HasOperation[RefRelease]:
end RefReleaseApi
class Skip(val _operation: Operation)
class Stop(val _operation: Operation)
class IntVerifAssert(val _operation: Operation)
class IntVerifAssume(val _operation: Operation)
class IntVerifCover(val _operation: Operation)
class When(val _operation: Operation)
trait WhenApi              extends HasOperation[When]:
end WhenApi
