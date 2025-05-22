// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.zaozi.mlirlib.tests

import org.llvm.mlir.scalalib.dialect.func.{Func, FuncApi, *, given}
import org.llvm.mlir.scalalib.dialect.smt.capi.{*, given}
import org.llvm.mlir.scalalib.dialect.smt.operation.{*, given}
import org.llvm.mlir.scalalib.{Module as MlirModule, ModuleApi as MlirModuleApi, TypeApi as _, *, given}
import utest.*

import java.lang.foreign.Arena

object SMTSmoke extends TestSuite:
  val tests: Tests = Tests:
    test("Load Panama Context"):
      val arena   = Arena.ofConfined()
      given Arena = arena
      test("Load Dialect"):
        val context         = summon[ContextApi].contextCreate
        context.loadSmtDialect()
        context.loadFuncDialect()
        given Context       = context
        val unknownLocation = summon[LocationApi].locationUnknownGet
        test("Smt"):
          given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(unknownLocation)
          val func: Func = summon[FuncApi].op("Func")
          func.appendToModule()
          given Block = func.block

          val boolType  = summon[TypeApi].getBool
          val funcType  = summon[TypeApi].getSMTFunc(Seq(boolType, boolType), boolType)
          val intType   = summon[TypeApi].getInt
          val arrayType = summon[TypeApi].getArray(intType, boolType)
          val bvType    = summon[TypeApi].getBitVector(1)

          val bool0  = summon[BoolConstantApi].op(false, location = unknownLocation).result
          val bool1  = summon[BoolConstantApi].op(true, location = unknownLocation).result
          val int0   = summon[IntConstantApi].op(0, location = unknownLocation).result
          val int1   = summon[IntConstantApi].op(1, location = unknownLocation).result
          val func0  = summon[DeclareFunApi].op("func0", location = unknownLocation, funcType).result
          val array0 = summon[DeclareFunApi].op("array0", location = unknownLocation, arrayType).result
          val bv0    = summon[BVConstantApi].op(0, 1, location = unknownLocation).result
          val bv1    = summon[BVConstantApi].op(1, 1, location = unknownLocation).result
          val bv10   = summon[BVConstantApi].op(2, 1, location = unknownLocation).result

          test("And"):
            summon[AndApi].op(Seq(bool0, bool1), unknownLocation).operation.appendToBlock()
          test("Array"):
            test("ApplyFunc"):
              summon[ApplyFuncApi].op(func0, Seq(bool0, bool1), unknownLocation).operation.appendToBlock()
            test("ArrayBroadcast"):
              summon[ArrayBroadcastApi].op(bool0, unknownLocation, arrayType).operation.appendToBlock()
            test("ArraySelect"):
              summon[ArraySelectApi].op(array0, int0, unknownLocation).operation.appendToBlock()
            test("ArrayStore"):
              summon[ArrayStoreApi].op(array0, int0, bool1, unknownLocation).operation.appendToBlock()
            test("Assert"):
              summon[AssertApi].op(bool0, unknownLocation).operation.appendToBlock()
          test("BV"):
            test("BV2Int"):
              summon[BV2IntApi].op(true, bv1, unknownLocation).operation.appendToBlock()
            test("BVAdd"):
              summon[BVAddApi].op(bv0, bv1, unknownLocation).operation.appendToBlock()
            test("BVCmp"):
              summon[BVCmpApi].op(bv0, bv1, "slt", unknownLocation).operation.appendToBlock()
            test("BVConstant"):
              summon[BVConstantApi].op(1, 1, unknownLocation).operation.appendToBlock()
            test("BVLShr"):
              summon[BVLShrApi].op(bv0, bv1, unknownLocation).operation.appendToBlock()
            test("BVMul"):
              summon[BVMulApi].op(bv0, bv1, unknownLocation).operation.appendToBlock()
            test("BVNeg"):
              summon[BVNegApi].op(bv0, unknownLocation).operation.appendToBlock()
            test("BVNot"):
              summon[BVNotApi].op(bv0, unknownLocation).operation.appendToBlock()
            test("BVOr"):
              summon[BVOrApi].op(bv0, bv1, unknownLocation).operation.appendToBlock()
            test("BVSDiv"):
              summon[BVSDivApi].op(bv0, bv1, unknownLocation).operation.appendToBlock()
            test("BVSMod"):
              summon[BVSModApi].op(bv0, bv1, unknownLocation).operation.appendToBlock()
            test("BVSRem"):
              summon[BVSRemApi].op(bv0, bv1, unknownLocation).operation.appendToBlock()
            test("BVShl"):
              summon[BVShlApi].op(bv0, bv1, unknownLocation).operation.appendToBlock()
            test("BVUDIV"):
              summon[BVUDivApi].op(bv0, bv1, unknownLocation).operation.appendToBlock()
            test("BVURem"):
              summon[BVURemApi].op(bv0, bv1, unknownLocation).operation.appendToBlock()
            test("BVXOr"):
              summon[BVXOrApi].op(bv0, bv1, unknownLocation).operation.appendToBlock()
          test("BoolConstant"):
            summon[BoolConstantApi].op(true, unknownLocation).operation.appendToBlock()
          test("Check"):
            summon[CheckApi].op(unknownLocation).operation.appendToBlock()
          test("Concat"):
            summon[ConcatApi].op(bv0, bv1, unknownLocation).operation.appendToBlock()
          test("DeclareFun"):
            summon[DeclareFunApi].op("a", unknownLocation, funcType).operation.appendToBlock()
          test("Distinct"):
            summon[DistinctApi].op(Seq(bool0, bool1), unknownLocation).operation.appendToBlock()
          test("Eq"):
            summon[EqApi].op(Seq(bool0, bool0), unknownLocation).operation.appendToBlock()
          test("Exists"):
            summon[ExistsApi].op(1, true, Seq("x", "y"), unknownLocation).operation.appendToBlock()
          test("Extract"):
            summon[ExtractApi].op(1, bv10, unknownLocation, bvType).operation.appendToBlock()
          test("Forall"):
            summon[ForallApi].op(1, true, Seq("x", "y"), unknownLocation).operation.appendToBlock()
          test("Implies"):
            summon[ImpliesApi].op(bool0, bool1, unknownLocation).operation.appendToBlock()
          test("Int"):
            test("Int2BV"):
              summon[Int2BVApi].op(int0, unknownLocation, bvType).operation.appendToBlock()
            test("IntAbs"):
              summon[IntAbsApi].op(int0, unknownLocation).operation.appendToBlock()
            test("IntAdd"):
              summon[IntAddApi].op(Seq(int0, int1), unknownLocation).operation.appendToBlock()
            test("IntCmp"):
              summon[IntCmpApi].op(int0, int1, "lt", unknownLocation).operation.appendToBlock()
            test("IntConstant"):
              summon[IntConstantApi].op(1, unknownLocation).operation.appendToBlock()
            test("IntDiv"):
              summon[IntDivApi].op(int0, int1, unknownLocation).operation.appendToBlock()
            test("IntMod"):
              summon[IntModApi].op(int0, int1, unknownLocation).operation.appendToBlock()
            test("IntMul"):
              summon[IntMulApi].op(Seq(int0, int1), unknownLocation).operation.appendToBlock()
            test("IntSub"):
              summon[IntSubApi].op(int1, int0, unknownLocation).operation.appendToBlock()
          test("Ite"):
            summon[IteApi].op(bool1, int0, int1, unknownLocation).operation.appendToBlock()
          test("Not"):
            summon[NotApi].op(bool0, unknownLocation).operation.appendToBlock()
          test("Or"):
            summon[OrApi].op(Seq(bool0, bool1), unknownLocation).operation.appendToBlock()
          test("Pop"):
            summon[PopApi].op(1, unknownLocation).operation.appendToBlock()
          test("Push"):
            summon[PushApi].op(1, unknownLocation).operation.appendToBlock()
          test("Repeat"):
            summon[RepeatApi].op(bv0, unknownLocation, summon[TypeApi].getBitVector(3)).operation.appendToBlock()
          test("Reset"):
            summon[ResetApi].op(unknownLocation).operation.appendToBlock()
          test("SetLogic"):
            summon[SetLogicApi].op("HORN", unknownLocation).operation.appendToBlock()
          test("Solver"):
            summon[SolverApi].op(unknownLocation).operation.appendToBlock()
          test("XOr"):
            summon[XOrApi].op(Seq(bool0, bool1), unknownLocation).operation.appendToBlock()
          test("Yield"):
            summon[YieldApi].op(Seq(bool0, bool1), unknownLocation).operation.appendToBlock()
