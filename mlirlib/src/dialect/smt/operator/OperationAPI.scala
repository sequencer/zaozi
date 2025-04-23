// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package org.llvm.mlir.scalalib.dialect.smt.operation

import org.llvm.mlir.scalalib.{HasOperation, Operation}

class And(val _operation: Operation)
trait AndApi extends HasOperation[And]
end AndApi

class ApplyFunc(val _operation: Operation)
trait ApplyFuncApi extends HasOperation[ApplyFunc]
end ApplyFuncApi

class ArrayBroadcast(val _operation: Operation)
trait ArrayBroadcastApi extends HasOperation[ArrayBroadcast]
end ArrayBroadcastApi

class ArraySelect(val _operation: Operation)
trait ArraySelectApi extends HasOperation[ArraySelect]
end ArraySelectApi

class ArrayStore(val _operation: Operation)
trait ArrayStoreApi extends HasOperation[ArrayStore]
end ArrayStoreApi

class Assert(val _operation: Operation)
trait AssertApi extends HasOperation[Assert]
end AssertApi

class BV2Int(val _operation: Operation)
trait BV2IntApi extends HasOperation[BV2Int]
end BV2IntApi

class BVAShr(val _operation: Operation)
trait BVAShrApi extends HasOperation[BVAShr]
end BVAShrApi

class BVAdd(val _operation: Operation)
trait BVAddApi extends HasOperation[BVAdd]
end BVAddApi

class BVAnd(val _operation: Operation)
trait BVAndApi extends HasOperation[BVAnd]
end BVAndApi

class BVCmp(val _operation: Operation)
trait BVCmpApi extends HasOperation[BVCmp]
end BVCmpApi

class BVConstant(val _operation: Operation)
trait BVConstantApi extends HasOperation[BVConstant]
end BVConstantApi

class BVLShr(val _operation: Operation)
trait BVLShrApi extends HasOperation[BVLShr]
end BVLShrApi

class BVMul(val _operation: Operation)
trait BVMulApi extends HasOperation[BVMul]
end BVMulApi

class BVNeg(val _operation: Operation)
trait BVNegApi extends HasOperation[BVNeg]
end BVNegApi

class BVNot(val _operation: Operation)
trait BVNotApi extends HasOperation[BVNot]
end BVNotApi

class BVOr(val _operation: Operation)
trait BVOrApi extends HasOperation[BVOr]
end BVOrApi

class BVSDiv(val _operation: Operation)
trait BVSDivApi extends HasOperation[BVSDiv]
end BVSDivApi

class BVSMod(val _operation: Operation)
trait BVSModApi extends HasOperation[BVSMod]
end BVSModApi

class BVSRem(val _operation: Operation)
trait BVSRemApi extends HasOperation[BVSRem]
end BVSRemApi

class BVShl(val _operation: Operation)
trait BVShlApi extends HasOperation[BVShl]
end BVShlApi

class BVUDiv(val _operation: Operation)
trait BVUDivApi extends HasOperation[BVUDiv]
end BVUDivApi

class BVURem(val _operation: Operation)
trait BVURemApi extends HasOperation[BVURem]
end BVURemApi

class BVXOr(val _operation: Operation)
trait BVXOrApi extends HasOperation[BVXOr]
end BVXOrApi

class BoolConstant(val _operation: Operation)
trait BoolConstantApi extends HasOperation[BoolConstant]
end BoolConstantApi

class Check(val _operation: Operation)
trait CheckApi extends HasOperation[Check]
end CheckApi

class Concat(val _operation: Operation)
trait ConcatApi extends HasOperation[Concat]
end ConcatApi

class DeclareFun(val _operation: Operation)
trait DeclareFunApi extends HasOperation[DeclareFun]
end DeclareFunApi

class Distinct(val _operation: Operation)
trait DistinctApi extends HasOperation[Distinct]
end DistinctApi

class Eq(val _operation: Operation)
trait EqApi extends HasOperation[Eq]
end EqApi

class Exists(val _operation: Operation)
trait ExistsApi extends HasOperation[Exists]
end ExistsApi

class Extract(val _operation: Operation)
trait ExtractApi extends HasOperation[Extract]
end ExtractApi

class Forall(val _operation: Operation)
trait ForallApi extends HasOperation[Forall]
end ForallApi

class Implies(val _operation: Operation)
trait ImpliesApi extends HasOperation[Implies]
end ImpliesApi

class Int2BV(val _operation: Operation)
trait Int2BVApi extends HasOperation[Int2BV]
end Int2BVApi

class IntAbs(val _operation: Operation)
trait IntAbsApi extends HasOperation[IntAbs]
end IntAbsApi

class IntAdd(val _operation: Operation)
trait IntAddApi extends HasOperation[IntAdd]
end IntAddApi

class IntCmp(val _operation: Operation)
trait IntCmpApi extends HasOperation[IntCmp]
end IntCmpApi

class IntConstant(val _operation: Operation)
trait IntConstantApi extends HasOperation[IntConstant]
end IntConstantApi

class IntDiv(val _operation: Operation)
trait IntDivApi extends HasOperation[IntDiv]
end IntDivApi

class IntMod(val _operation: Operation)
trait IntModApi extends HasOperation[IntMod]
end IntModApi

class IntMul(val _operation: Operation)
trait IntMulApi extends HasOperation[IntMul]
end IntMulApi

class IntSub(val _operation: Operation)
trait IntSubApi extends HasOperation[IntSub]
end IntSubApi

class Ite(val _operation: Operation)
trait IteApi extends HasOperation[Ite]
end IteApi

class Not(val _operation: Operation)
trait NotApi extends HasOperation[Not]
end NotApi

class Or(val _operation: Operation)
trait OrApi extends HasOperation[Or]
end OrApi

class Pop(val _operation: Operation)
trait PopApi extends HasOperation[Pop]
end PopApi

class Push(val _operation: Operation)
trait PushApi extends HasOperation[Push]
end PushApi

class Repeat(val _operation: Operation)
trait RepeatApi extends HasOperation[Repeat]
end RepeatApi

class Reset(val _operation: Operation)
trait ResetApi extends HasOperation[Reset]
end ResetApi

class SetLogic(val _operation: Operation)
trait SetLogicApi extends HasOperation[SetLogic]
end SetLogicApi

class Solver(val _operation: Operation)
trait SolverApi extends HasOperation[Solver]
end SolverApi

class XOr(val _operation: Operation)
trait XOrApi extends HasOperation[XOr]
end XOrApi

class Yield(val _operation: Operation)
trait YieldApi extends HasOperation[Yield]
end YieldApi
