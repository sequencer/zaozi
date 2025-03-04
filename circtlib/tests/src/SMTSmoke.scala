// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.circtlib.tests

import org.llvm.circt.scalalib.smt.capi.given_DialectHandleApi
import org.llvm.circt.scalalib.smt.operation.{*, given}
import org.llvm.mlir.scalalib.{Module as MlirModule, ModuleApi as MlirModuleApi, *, given}
import utest.*

import java.lang.foreign.Arena

object SMTSmoke extends TestSuite:
  val tests = Tests:
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
          val bool0   = summon[BoolConstantApi].op(false, location = unknownLocation)
          val bool1   = summon[BoolConstantApi].op(true, location = unknownLocation)
          test("And"):
            summon[AndApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("ApplyFunc"):
          //   summon[ApplyFuncApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("ArrayBroadcast"):
          //   summon[ArrayBroadcastApi].op(bool0.result, unknownLocation).operation.appendToBlock()
          // test("ArraySelect"):
          //   summon[ArraySelectApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("ArrayStore"):
          //   summon[ArrayStoreApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("BV2Int"):
          //   summon[BV2IntApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("BVAdd"):
          //   summon[BVAddApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("BVCmp"):
          //   summon[BVCmpApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("BVLShr"):
          //   summon[BVLShrApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("BVNeg"):
          //   summon[BVNegApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("BVOr"):
          //   summon[BVOrApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("BVSMod"):
          //   summon[BVSModApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("BVShl"):
          //   summon[BVShlApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("BVURem"):
          //   summon[BVURemApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("BoolConstant"):
          //   summon[BoolConstantApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("Concat"):
          //   summon[ConcatApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("Distinct"):
          //   summon[DistinctApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("Exists"):
          //   summon[ExistsApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("Forall"):
          //   summon[ForallApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("Int2BV"):
          //   summon[Int2BVApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("IntAdd"):
          //   summon[IntAddApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("IntConstant"):
          //   summon[IntConstantApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("IntMod"):
          //   summon[IntModApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("IntSub"):
          //   summon[IntSubApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("Not"):
          //   summon[NotApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("Pop"):
          //   summon[PopApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("Repeat"):
          //   summon[RepeatApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("SetLogic"):
          //   summon[SetLogicApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
          // test("XOr"):
          //   summon[XOrApi].op(Seq(bool0.result, bool1.result), unknownLocation).operation.appendToBlock()
