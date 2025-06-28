// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package org.llvm.circt.scalalib.dialect.firrtl.operation

import org.llvm.mlir.scalalib.capi.support.HasOperation
import org.llvm.mlir.scalalib.capi.ir.Operation

class ClockDividerIntrinsic(val _operation: Operation)
class ClockGateIntrinsic(val _operation: Operation)
class ClockInverterIntrinsic(val _operation: Operation)
class DPICallIntrinsic(val _operation: Operation)
class FPGAProbeIntrinsic(val _operation: Operation)
class GenericIntrinsic(val _operation: Operation)
class HasBeenResetIntrinsic(val _operation: Operation)
class IsXIntrinsic(val _operation: Operation)
class PlusArgsTestIntrinsic(val _operation: Operation)
class PlusArgsValueIntrinsic(val _operation: Operation)
class UnclockedAssumeIntrinsic(val _operation: Operation)

class LTLAndIntrinsic(val _operation: Operation)
trait LTLAndIntrinsicApi extends HasOperation[LTLAndIntrinsic]
end LTLAndIntrinsicApi

class LTLClockIntrinsic(val _operation: Operation)
trait LTLClockIntrinsicApi extends HasOperation[LTLClockIntrinsic]
end LTLClockIntrinsicApi

class LTLConcatIntrinsic(val _operation: Operation)
trait LTLConcatIntrinsicApi extends HasOperation[LTLConcatIntrinsic]
end LTLConcatIntrinsicApi

class LTLDelayIntrinsic(val _operation: Operation)
trait LTLDelayIntrinsicApi extends HasOperation[LTLDelayIntrinsic]
end LTLDelayIntrinsicApi

class LTLEventuallyIntrinsic(val _operation: Operation)
trait LTLEventuallyIntrinsicApi extends HasOperation[LTLEventuallyIntrinsic]
end LTLEventuallyIntrinsicApi

class LTLGoToRepeatIntrinsic(val _operation: Operation)
trait LTLGoToRepeatIntrinsicApi extends HasOperation[LTLGoToRepeatIntrinsic]
end LTLGoToRepeatIntrinsicApi

class LTLImplicationIntrinsic(val _operation: Operation)
trait LTLImplicationIntrinsicApi extends HasOperation[LTLImplicationIntrinsic]
end LTLImplicationIntrinsicApi

class LTLIntersectIntrinsic(val _operation: Operation)
trait LTLIntersectIntrinsicApi extends HasOperation[LTLIntersectIntrinsic]
end LTLIntersectIntrinsicApi

class LTLNonConsecutiveRepeatIntrinsic(val _operation: Operation)
trait LTLNonConsecutiveRepeatIntrinsicApi extends HasOperation[LTLNonConsecutiveRepeatIntrinsic]
end LTLNonConsecutiveRepeatIntrinsicApi

class LTLNotIntrinsic(val _operation: Operation)
trait LTLNotIntrinsicApi extends HasOperation[LTLNotIntrinsic]
end LTLNotIntrinsicApi

class LTLOrIntrinsic(val _operation: Operation)
trait LTLOrIntrinsicApi extends HasOperation[LTLOrIntrinsic]
end LTLOrIntrinsicApi

class LTLRepeatIntrinsic(val _operation: Operation)
trait LTLRepeatIntrinsicApi extends HasOperation[LTLRepeatIntrinsic]
end LTLRepeatIntrinsicApi

class LTLUntilIntrinsic(val _operation: Operation)
trait LTLUntilIntrinsicApi extends HasOperation[LTLUntilIntrinsic]
end LTLUntilIntrinsicApi

class VerifAssertIntrinsic(val _operation: Operation)
trait VerifAssertIntrinsicApi extends HasOperation[VerifAssertIntrinsic]
end VerifAssertIntrinsicApi

class VerifAssumeIntrinsic(val _operation: Operation)
trait VerifAssumeIntrinsicApi extends HasOperation[VerifAssumeIntrinsic]
end VerifAssumeIntrinsicApi

class VerifCoverIntrinsic(val _operation: Operation)
trait VerifCoverIntrinsicApi extends HasOperation[VerifCoverIntrinsic]
end VerifCoverIntrinsicApi

class VerifEnsureIntrinsic(val _operation: Operation)
trait VerifEnsureIntrinsicApi extends HasOperation[VerifEnsureIntrinsic]
end VerifEnsureIntrinsicApi

class VerifRequireIntrinsic(val _operation: Operation)
trait VerifRequireIntrinsicApi extends HasOperation[VerifRequireIntrinsic]
end VerifRequireIntrinsicApi
