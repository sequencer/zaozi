// SPDX-License-Identifier: Apache-2.0
package me.jiuyang.zaozi.circtlib

import org.llvm.circt
import org.llvm.circt.CAPI

import java.lang.foreign.{Arena, MemorySegment}
import java.lang.foreign.MemorySegment.NULL

/** It natively links from Scala to native library. */
class CirctHandler:
  private val arena = Arena.ofConfined()

  private val mlirCtx =
    val mlirCtx = CAPI.mlirContextCreate(arena)

    // Register dialects
    Seq(
      CAPI.mlirGetDialectHandle__firrtl__(arena),
      CAPI.mlirGetDialectHandle__chirrtl__(arena),
      CAPI.mlirGetDialectHandle__sv__(arena),
      CAPI.mlirGetDialectHandle__seq__(arena),
      CAPI.mlirGetDialectHandle__emit__(arena)
    ).foreach(CAPI.mlirDialectHandleLoadDialect(arena, _, mlirCtx))

    mlirCtx

  class Region(val region: MlirRegion, val blocks: Seq[MlirBlock]):
    def get(): MlirRegion = region
    def block(i: Int): MlirBlock = blocks(i)

  class Op(val state: MlirOperationState, val op: MlirOperation, val regions: Seq[Region], val results: Seq[MlirValue]):
    def region(i: Int): Region = regions(i)

  class OpBuilder(val opName: String, val parent: MlirBlock, val loc: MlirLocation):
    var regionsBlocks:   Seq[Option[Seq[(Seq[MlirType], Seq[MlirLocation])]]] = Seq.empty
    var attrs:           Seq[MlirNamedAttribute]                              = Seq.empty
    var operands:        Seq[MlirValue]                                       = Seq.empty
    var results:         Seq[MlirType]                                        = Seq.empty
    var resultInference: Option[Int]                                          = None

    def withRegion(block: Seq[(Seq[MlirType], Seq[MlirLocation])]):        OpBuilder =
      regionsBlocks = regionsBlocks :+ Some(block)
      this
    def withRegionNoBlock():                                               OpBuilder =
      regionsBlocks = regionsBlocks :+ None
      this
    def withRegions(blocks: Seq[Seq[(Seq[MlirType], Seq[MlirLocation])]]): OpBuilder =
      regionsBlocks = regionsBlocks ++ blocks.map(Some(_))
      this
    def withNamedAttr(name: String, attr: MlirAttribute):                  OpBuilder =
      attrs = attrs :+ mlirNamedAttributeGet(name, attr)
      this
    def withNamedAttrs(as: Seq[(String, MlirAttribute)]):                  OpBuilder =
      as.foreach(a => withNamedAttr(a._1, a._2))
      this
    def withOperand(o: MlirValue):                                         OpBuilder =
      operands = operands :+ o;
      this
    def withOperands(os: Seq[MlirValue]):                                  OpBuilder =
      operands = operands ++ os;
      this
    def withResult(r: MlirType):                                           OpBuilder =
      results = results :+ r;
      this
    def withResults(rs: Seq[MlirType]):                                    OpBuilder =
      results = results ++ rs;
      this
    def withResultInference(expectedCount: Int):                           OpBuilder =
      resultInference = Some(expectedCount);
      this
    private def buildImpl(inserter: MlirOperation => Unit):                Op        =
      val state = mlirOperationStateGet(opName, loc)

      mlirOperationStateAddAttributes(state, attrs)
      mlirOperationStateAddOperands(state, operands)
      if (resultInference.isEmpty)
        mlirOperationStateAddResults(state, results)
      else
        mlirOperationStateEnableResultTypeInference(state)

      val builtRegions = regionsBlocks.foldLeft(Seq.empty[Region]):
        case (builtRegions, blocks) =>
          val region = mlirRegionCreate()
          if (blocks.nonEmpty)
            val builtBlocks = blocks.get.map:
              case (blockArgTypes, blockArgLocs) =>
                val block = mlirBlockCreate(blockArgTypes, blockArgLocs)
                mlirRegionAppendOwnedBlock(region, block)
                block
            builtRegions :+ Region(region, builtBlocks)
          else builtRegions :+ Region(region, Seq.empty)

      mlirOperationStateAddOwnedRegions(state, builtRegions.map(_.region))

      val op = mlirOperationCreate(state)
      inserter(op)

      val resultVals = (0 until resultInference.getOrElse(results.length)).map(
        mlirOperationGetResult(op, _)
      )

      Op(state, op, builtRegions, resultVals)
    def build():                                                           Op        = buildImpl(mlirBlockAppendOwnedOperation(parent, _))
    def buildAfter(ref:  Op): Op = buildImpl(mlirBlockInsertOwnedOperationAfter(parent, ref.op, _))
    def buildBefore(ref: Op): Op = buildImpl(mlirBlockInsertOwnedOperationBefore(parent, ref.op, _))

  // Constants for this instance
  val unkLoc:         MlirLocation  = mlirLocationUnknownGet()
  val emptyArrayAttr: MlirAttribute = mlirArrayAttrGet(Seq.empty)

  //////////////////////////////////////////////////
  // Helpers
  //

  private def newString(string: String): MlirStringRef =
    val bytes  = string.getBytes()
    val buffer = arena.allocate(bytes.length + 1)
    buffer.copyFrom(MemorySegment.ofArray(bytes))
    MlirStringRef(CAPI.mlirStringRefCreateFromCString(arena, buffer))

  private def stringRefFromBytes(bytes: Array[Byte]): MlirStringRef =
    val buffer = arena.allocate(bytes.length)
    buffer.copyFrom(MemorySegment.ofArray(bytes))

    val stringRef = circt.MlirStringRef.allocate(arena)
    circt.MlirStringRef.data$set(stringRef, buffer)
    circt.MlirStringRef.length$set(stringRef, bytes.length)

    MlirStringRef(stringRef)

  private def newStringCallback(callback: String => Unit): MlirStringCallback =
    val cb = new circt.MlirStringCallback:
      def apply(message: MemorySegment, userData: MemorySegment): Unit =
        callback(MlirStringRef(message).toString)

    MlirStringCallback(circt.MlirStringCallback.allocate(cb, arena))

  private def seqToArray[T <: ForeignType[?]](xs: Seq[T]): (MemorySegment, Int) =
    if (xs.nonEmpty)
      val sizeOfT = xs.head.sizeof

      val buffer = arena.allocate(sizeOfT * xs.length)
      xs.zipWithIndex.foreach:
        case (x, i) =>
          x.get match
            case value: MemorySegment => buffer.asSlice(sizeOfT * i, sizeOfT).copyFrom(value)
            case value: Int           => buffer.setAtIndex(CAPI.C_INT, i, value)

      (buffer, xs.length)
    else (NULL, 0)

  //////////////////////////////////////////////////
  // CIRCT APIs
  //

  def mlirModuleCreateEmpty(location: MlirLocation): MlirModule = MlirModule(
    CAPI.mlirModuleCreateEmpty(arena, location.get)
  )

  def mlirModuleCreateParse(module: String):           MlirModule = MlirModule(
    CAPI.mlirModuleCreateParse(arena, mlirCtx, newString(module).get)
  )

  def mlirModuleCreateParseBytes(module: Array[Byte]): MlirModule = MlirModule(
    CAPI.mlirModuleCreateParse(arena, mlirCtx, stringRefFromBytes(module).get)
  )

  def mlirModuleFromOperation(op: MlirOperation): MlirModule = MlirModule(CAPI.mlirModuleFromOperation(arena, op.get))

  def mlirModuleGetBody(module: MlirModule): MlirBlock = MlirBlock(CAPI.mlirModuleGetBody(arena, module.get))

  def mlirModuleGetOperation(module: MlirModule): MlirOperation = MlirOperation(
    CAPI.mlirModuleGetOperation(arena, module.get)
  )

  def mlirOperationStateGet(name: String, loc: MlirLocation): MlirOperationState = MlirOperationState(
    CAPI.mlirOperationStateGet(arena, newString(name).get, loc.get)
  )

  def mlirOperationStateAddAttributes(state: MlirOperationState, attrs: Seq[MlirNamedAttribute]): Any =
    if (attrs.nonEmpty)
      val (ptr, length) = seqToArray(attrs)
      CAPI.mlirOperationStateAddAttributes(state.get, length, ptr)

  def mlirAttributeDump(attr: MlirAttribute): Any = CAPI.mlirAttributeDump(attr.get)

  def mlirOperationStateAddOperands(state: MlirOperationState, operands: Seq[MlirValue]): Any =
    if (operands.nonEmpty)
      val (ptr, length) = seqToArray(operands)
      CAPI.mlirOperationStateAddOperands(state.get, length, ptr)

  def mlirOperationStateAddResults(state: MlirOperationState, results: Seq[MlirType]): Any =
    if (results.nonEmpty)
      val (ptr, length) = seqToArray(results)
      CAPI.mlirOperationStateAddResults(state.get, length, ptr)

  def mlirOperationStateAddOwnedRegions(state: MlirOperationState, regions: Seq[MlirRegion]): Any =
    if (regions.nonEmpty)
      val (ptr, length) = seqToArray(regions)
      CAPI.mlirOperationStateAddOwnedRegions(state.get, length, ptr)

  def mlirOperationStateEnableResultTypeInference(state: MlirOperationState): Unit =
    CAPI.mlirOperationStateEnableResultTypeInference(state.get)

  def mlirOperationCreate(state: MlirOperationState): MlirOperation = MlirOperation(
    CAPI.mlirOperationCreate(arena, state.get)
  )

  def mlirOperationGetResult(operation: MlirOperation, pos: Long): MlirValue = MlirValue(
    CAPI.mlirOperationGetResult(arena, operation.get, pos)
  )

  def mlirOperationGetAttributeByName(op: MlirOperation, name: String): MlirAttribute = MlirAttribute(
    CAPI.mlirOperationGetAttributeByName(arena, op.get, newString(name).get)
  )

  def mlirOperationSetInherentAttributeByName(op: MlirOperation, name: String, attr: MlirAttribute): Unit =
    CAPI.mlirOperationSetInherentAttributeByName(op.get, newString(name).get, attr.get)

  def mlirBlockCreate(args: Seq[MlirType], locs: Seq[MlirLocation]): MlirBlock =
    assert(args.length == locs.length)
    val length = args.length
    MlirBlock(CAPI.mlirBlockCreate(arena, length, seqToArray(args)._1, seqToArray(locs)._1))

  def mlirBlockGetArgument(block: MlirBlock, pos: Long): MlirValue = MlirValue(
    CAPI.mlirBlockGetArgument(arena, block.get, pos)
  )

  def mlirBlockGetFirstOperation(block: MlirBlock): MlirOperation = MlirOperation(
    CAPI.mlirBlockGetFirstOperation(arena, block.get)
  )

  def mlirBlockAppendOwnedOperation(block: MlirBlock, operation: MlirOperation): Any =
    CAPI.mlirBlockAppendOwnedOperation(block.get, operation.get)

  def mlirBlockInsertOwnedOperationAfter(block: MlirBlock, reference: MlirOperation, operation: MlirOperation): Any =
    CAPI.mlirBlockInsertOwnedOperationAfter(block.get, reference.get, operation.get)

  def mlirBlockInsertOwnedOperationBefore(block: MlirBlock, reference: MlirOperation, operation: MlirOperation): Any =
    CAPI.mlirBlockInsertOwnedOperationBefore(block.get, reference.get, operation.get)

  def mlirRegionCreate(): MlirRegion = MlirRegion(CAPI.mlirRegionCreate(arena))

  def mlirRegionAppendOwnedBlock(region: MlirRegion, block: MlirBlock): Any =
    CAPI.mlirRegionAppendOwnedBlock(region.get, block.get)

  def mlirLocationGetAttribute(loc: MlirLocation): MlirAttribute = MlirAttribute(
    CAPI.mlirLocationGetAttribute(arena, loc.get)
  )

  def mlirLocationUnknownGet(): MlirLocation = MlirLocation(CAPI.mlirLocationUnknownGet(arena, mlirCtx))

  def mlirLocationFileLineColGet(filename: String, line: Int, col: Int): MlirLocation = MlirLocation(
    CAPI.mlirLocationFileLineColGet(arena, mlirCtx, newString(filename).get, line, col)
  )

  def mlirIdentifierGet(string: String): MlirIdentifier = MlirIdentifier(
    CAPI.mlirIdentifierGet(arena, mlirCtx, newString(string).get)
  )

  def mlirNamedAttributeGet(name: String, attr: MlirAttribute): MlirNamedAttribute = MlirNamedAttribute(
    CAPI.mlirNamedAttributeGet(arena, mlirIdentifierGet(name).get, attr.get)
  )

  def mlirArrayAttrGet(elements: Seq[MlirAttribute]): MlirAttribute =
    val (ptr, length) = seqToArray(elements)
    MlirAttribute(CAPI.mlirArrayAttrGet(arena, mlirCtx, length, ptr))

  def mlirArrayAttrGetNumElements(attr: MlirAttribute): Long = CAPI.mlirArrayAttrGetNumElements(attr.get)

  def mlirArrayAttrGetElement(attr: MlirAttribute, pos: Long): MlirAttribute = MlirAttribute(
    CAPI.mlirArrayAttrGetElement(arena, attr.get, pos)
  )

  def mlirTypeAttrGet(tpe: MlirType): MlirAttribute = MlirAttribute(CAPI.mlirTypeAttrGet(arena, tpe.get))

  def mlirBoolAttrGet(value: Boolean): MlirAttribute = MlirAttribute(
    CAPI.mlirBoolAttrGet(arena, mlirCtx, if (value) 1 else 0)
  )

  def mlirStringAttrGet(string: String): MlirAttribute = MlirAttribute(
    CAPI.mlirStringAttrGet(arena, mlirCtx, newString(string).get)
  )

  def mlirStringAttrGetValue(attr: MlirAttribute): String =
    val string = CAPI.mlirStringAttrGetValue(arena, attr.get)
    MlirStringRef(string).toString

  def mlirAttributeIsAInteger(attr: MlirAttribute): Boolean = CAPI.mlirAttributeIsAInteger(attr.get)

  def mlirAttributeIsAString(attr: MlirAttribute): Boolean = CAPI.mlirAttributeIsAString(attr.get)

  def mlirIntegerAttrGet(tpe: MlirType, value: Long): MlirAttribute = MlirAttribute(
    CAPI.mlirIntegerAttrGet(arena, tpe.get, value)
  )

  def mlirIntegerAttrGetValueInt(attr: MlirAttribute): Long = CAPI.mlirIntegerAttrGetValueInt(attr.get)

  def mlirIntegerAttrGetValueSInt(attr: MlirAttribute): Long = CAPI.mlirIntegerAttrGetValueSInt(attr.get)

  def mlirIntegerAttrGetValueUInt(attr: MlirAttribute): Long = CAPI.mlirIntegerAttrGetValueUInt(attr.get)

  def mlirFloatAttrDoubleGet(tpe: MlirType, value: Double): MlirAttribute = MlirAttribute(
    CAPI.mlirFloatAttrDoubleGet(arena, mlirCtx, tpe.get, value)
  )

  def mlirFlatSymbolRefAttrGet(symbol: String): MlirAttribute = MlirAttribute(
    CAPI.mlirFlatSymbolRefAttrGet(arena, mlirCtx, newString(symbol).get)
  )

  def mlirValueGetType(tpe: MlirValue): MlirType = MlirType(CAPI.mlirValueGetType(arena, tpe.get))

  def mlirNoneTypeGet(): MlirType = MlirType(CAPI.mlirNoneTypeGet(arena, mlirCtx))

  def mlirIntegerTypeGet(bitwidth: Int): MlirType = MlirType(CAPI.mlirIntegerTypeGet(arena, mlirCtx, bitwidth))

  def mlirIntegerTypeUnsignedGet(bitwidth: Int): MlirType = MlirType(
    CAPI.mlirIntegerTypeUnsignedGet(arena, mlirCtx, bitwidth)
  )

  def mlirIntegerTypeSignedGet(bitwidth: Int): MlirType = MlirType(
    CAPI.mlirIntegerTypeSignedGet(arena, mlirCtx, bitwidth)
  )

  def mlirF64TypeGet(): MlirType = MlirType(CAPI.mlirF64TypeGet(arena, mlirCtx))

  def mlirOperationPrint(op: MlirOperation, callback: String => Unit): Any =
    CAPI.mlirOperationPrint(op.get, newStringCallback(callback).get, NULL)

  def mlirOperationWriteBytecode(op: MlirOperation, callback: Array[Byte] => Unit): Any =
    val cb = new circt.MlirStringCallback:
      def apply(message: MemorySegment, userData: MemorySegment): Unit =
        callback(MlirStringRef(message).toBytes)

    val mlirCallback = MlirStringCallback(circt.MlirStringCallback.allocate(cb, arena))
    CAPI.mlirOperationWriteBytecode(op.get, mlirCallback.get, NULL)

  def mlirExportFIRRTL(module: MlirModule, callback: String => Unit): Any =
    CAPI.mlirExportFIRRTL(arena, module.get, newStringCallback(callback).get, NULL)

  def mlirPassManagerCreate(): MlirPassManager = MlirPassManager(CAPI.mlirPassManagerCreate(arena, mlirCtx))

  def mlirPassManagerAddOwnedPass(pm: MlirPassManager, pass: MlirPass): Any =
    CAPI.mlirPassManagerAddOwnedPass(pm.get, pass.get)

  def mlirPassManagerGetNestedUnder(pm: MlirPassManager, operationName: String): MlirOpPassManager = MlirOpPassManager(
    CAPI.mlirPassManagerGetNestedUnder(arena, pm.get, newString(operationName).get)
  )

  def mlirPassManagerRunOnOp(pm: MlirPassManager, op: MlirOperation): MlirLogicalResult = MlirLogicalResult(
    CAPI.mlirPassManagerRunOnOp(arena, pm.get, op.get)
  )

  def mlirOpPassManagerAddOwnedPass(pm: MlirOpPassManager, pass: MlirPass): Any =
    CAPI.mlirOpPassManagerAddOwnedPass(pm.get, pass.get)

  def mlirOpPassManagerGetNestedUnder(pm: MlirOpPassManager, operationName: String): MlirOpPassManager =
    MlirOpPassManager(
      CAPI.mlirOpPassManagerGetNestedUnder(arena, pm.get, newString(operationName).get)
    )

  def circtFirtoolOptionsCreateDefault():                                                                         CirctFirtoolFirtoolOptions = CirctFirtoolFirtoolOptions(
    CAPI.circtFirtoolOptionsCreateDefault(arena)
  )
  def circtFirtoolOptionsDestroy(options: CirctFirtoolFirtoolOptions):                                            Any                        =
    CAPI.circtFirtoolOptionsDestroy(options.get)
  def circtFirtoolOptionsSetOutputFilename(options: CirctFirtoolFirtoolOptions, value: String):                   Any                        =
    CAPI.circtFirtoolOptionsSetOutputFilename(options.get, newString(value).get)
  def circtFirtoolOptionsSetDisableUnknownAnnotations(options: CirctFirtoolFirtoolOptions, value: Boolean):       Any                        =
    CAPI.circtFirtoolOptionsSetDisableUnknownAnnotations(options.get, value)
  def circtFirtoolOptionsSetDisableAnnotationsClassless(options: CirctFirtoolFirtoolOptions, value: Boolean):     Any                        =
    CAPI.circtFirtoolOptionsSetDisableAnnotationsClassless(options.get, value)
  def circtFirtoolOptionsSetLowerAnnotationsNoRefTypePorts(options: CirctFirtoolFirtoolOptions, value: Boolean):  Any                        =
    CAPI.circtFirtoolOptionsSetLowerAnnotationsNoRefTypePorts(options.get, value)
  def circtFirtoolOptionsSetPreserveAggregate(
    options: CirctFirtoolFirtoolOptions,
    value:   CirctFirtoolPreserveAggregateMode
  ): Any = CAPI.circtFirtoolOptionsSetPreserveAggregate(options.get, value.get)
  def circtFirtoolOptionsSetPreserveValues(options: CirctFirtoolFirtoolOptions, value: CirctFirtoolPreserveValuesMode)
    : Any =
    CAPI.circtFirtoolOptionsSetPreserveValues(options.get, value.get)
  def circtFirtoolOptionsSetBuildMode(options: CirctFirtoolFirtoolOptions, value: CirctFirtoolBuildMode):         Any                        =
    CAPI.circtFirtoolOptionsSetBuildMode(options.get, value.get)
  def circtFirtoolOptionsSetDisableOptimization(options: CirctFirtoolFirtoolOptions, value: Boolean):             Any                        =
    CAPI.circtFirtoolOptionsSetDisableOptimization(options.get, value)
  def circtFirtoolOptionsSetExportChiselInterface(options: CirctFirtoolFirtoolOptions, value: Boolean):           Any                        =
    CAPI.circtFirtoolOptionsSetExportChiselInterface(options.get, value)
  def circtFirtoolOptionsSetChiselInterfaceOutDirectory(options: CirctFirtoolFirtoolOptions, value: String):      Any                        =
    CAPI.circtFirtoolOptionsSetChiselInterfaceOutDirectory(options.get, newString(value).get)
  def circtFirtoolOptionsSetVbToBv(options: CirctFirtoolFirtoolOptions, value: Boolean):                          Any                        =
    CAPI.circtFirtoolOptionsSetVbToBv(options.get, value)
  def circtFirtoolOptionsSetNoDedup(options: CirctFirtoolFirtoolOptions, value: Boolean):                         Any                        =
    CAPI.circtFirtoolOptionsSetNoDedup(options.get, value)
  def circtFirtoolOptionsSetCompanionMode(options: CirctFirtoolFirtoolOptions, value: CirctFirtoolCompanionMode): Any                        =
    CAPI.circtFirtoolOptionsSetCompanionMode(options.get, value.get)
  def circtFirtoolOptionsSetDisableAggressiveMergeConnections(options: CirctFirtoolFirtoolOptions, value: Boolean)
    : Any =
    CAPI.circtFirtoolOptionsSetDisableAggressiveMergeConnections(options.get, value)
  def circtFirtoolOptionsSetLowerMemories(options: CirctFirtoolFirtoolOptions, value: Boolean):                   Any                        =
    CAPI.circtFirtoolOptionsSetLowerMemories(options.get, value)
  def circtFirtoolOptionsSetBlackBoxRootPath(options: CirctFirtoolFirtoolOptions, value: String):                 Any                        =
    CAPI.circtFirtoolOptionsSetBlackBoxRootPath(options.get, newString(value).get)
  def circtFirtoolOptionsSetReplSeqMem(options: CirctFirtoolFirtoolOptions, value: Boolean):                      Any                        =
    CAPI.circtFirtoolOptionsSetReplSeqMem(options.get, value)
  def circtFirtoolOptionsSetReplSeqMemFile(options: CirctFirtoolFirtoolOptions, value: String):                   Any                        =
    CAPI.circtFirtoolOptionsSetReplSeqMemFile(options.get, newString(value).get)
  def circtFirtoolOptionsSetExtractTestCode(options: CirctFirtoolFirtoolOptions, value: Boolean):                 Any                        =
    CAPI.circtFirtoolOptionsSetExtractTestCode(options.get, value)
  def circtFirtoolOptionsSetIgnoreReadEnableMem(options: CirctFirtoolFirtoolOptions, value: Boolean):             Any                        =
    CAPI.circtFirtoolOptionsSetIgnoreReadEnableMem(options.get, value)
  def circtFirtoolOptionsSetDisableRandom(options: CirctFirtoolFirtoolOptions, value: CirctFirtoolRandomKind):    Any                        =
    CAPI.circtFirtoolOptionsSetDisableRandom(options.get, value.get)
  def circtFirtoolOptionsSetOutputAnnotationFilename(options: CirctFirtoolFirtoolOptions, value: String):         Any                        =
    CAPI.circtFirtoolOptionsSetOutputAnnotationFilename(options.get, newString(value).get)
  def circtFirtoolOptionsSetEnableAnnotationWarning(options: CirctFirtoolFirtoolOptions, value: Boolean):         Any                        =
    CAPI.circtFirtoolOptionsSetEnableAnnotationWarning(options.get, value)
  def circtFirtoolOptionsSetAddMuxPragmas(options: CirctFirtoolFirtoolOptions, value: Boolean):                   Any                        =
    CAPI.circtFirtoolOptionsSetAddMuxPragmas(options.get, value)
  def circtFirtoolOptionsSetVerificationFlavor(
    options: CirctFirtoolFirtoolOptions,
    value:   CirctFirtoolVerificationFlavor
  ): Any =
    CAPI.circtFirtoolOptionsSetVerificationFlavor(options.get, value.get)
  def circtFirtoolOptionsSetEmitSeparateAlwaysBlocks(options: CirctFirtoolFirtoolOptions, value: Boolean):        Any                        =
    CAPI.circtFirtoolOptionsSetEmitSeparateAlwaysBlocks(options.get, value)
  def circtFirtoolOptionsSetEtcDisableInstanceExtraction(options: CirctFirtoolFirtoolOptions, value: Boolean):    Any                        =
    CAPI.circtFirtoolOptionsSetEtcDisableInstanceExtraction(options.get, value)
  def circtFirtoolOptionsSetEtcDisableRegisterExtraction(options: CirctFirtoolFirtoolOptions, value: Boolean):    Any                        =
    CAPI.circtFirtoolOptionsSetEtcDisableRegisterExtraction(options.get, value)
  def circtFirtoolOptionsSetEtcDisableModuleInlining(options: CirctFirtoolFirtoolOptions, value: Boolean):        Any                        =
    CAPI.circtFirtoolOptionsSetEtcDisableModuleInlining(options.get, value)
  def circtFirtoolOptionsSetAddVivadoRAMAddressConflictSynthesisBugWorkaround(
    options: CirctFirtoolFirtoolOptions,
    value:   Boolean
  ): Any = CAPI.circtFirtoolOptionsSetAddVivadoRAMAddressConflictSynthesisBugWorkaround(options.get, value)
  def circtFirtoolOptionsSetCkgModuleName(options: CirctFirtoolFirtoolOptions, value: String):                    Any                        =
    CAPI.circtFirtoolOptionsSetCkgModuleName(options.get, newString(value).get)
  def circtFirtoolOptionsSetCkgInputName(options: CirctFirtoolFirtoolOptions, value: String):                     Any                        =
    CAPI.circtFirtoolOptionsSetCkgInputName(options.get, newString(value).get)
  def circtFirtoolOptionsSetCkgOutputName(options: CirctFirtoolFirtoolOptions, value: String):                    Any                        =
    CAPI.circtFirtoolOptionsSetCkgOutputName(options.get, newString(value).get)
  def circtFirtoolOptionsSetCkgEnableName(options: CirctFirtoolFirtoolOptions, value: String):                    Any                        =
    CAPI.circtFirtoolOptionsSetCkgEnableName(options.get, newString(value).get)
  def circtFirtoolOptionsSetCkgTestEnableName(options: CirctFirtoolFirtoolOptions, value: String):                Any                        =
    CAPI.circtFirtoolOptionsSetCkgTestEnableName(options.get, newString(value).get)
  def circtFirtoolOptionsSetExportModuleHierarchy(options: CirctFirtoolFirtoolOptions, value: Boolean):           Any                        =
    CAPI.circtFirtoolOptionsSetExportModuleHierarchy(options.get, value)
  def circtFirtoolOptionsSetStripFirDebugInfo(options: CirctFirtoolFirtoolOptions, value: Boolean):               Any                        =
    CAPI.circtFirtoolOptionsSetStripFirDebugInfo(options.get, value)
  def circtFirtoolOptionsSetStripDebugInfo(options: CirctFirtoolFirtoolOptions, value: Boolean):                  Any                        =
    CAPI.circtFirtoolOptionsSetStripDebugInfo(options.get, value)

  def circtFirtoolPopulatePreprocessTransforms(pm: MlirPassManager, options: CirctFirtoolFirtoolOptions)
    : MlirLogicalResult =
    MlirLogicalResult(
      CAPI.circtFirtoolPopulatePreprocessTransforms(arena, pm.get, options.get)
    )

  def circtFirtoolPopulateCHIRRTLToLowFIRRTL(
    pm:            MlirPassManager,
    options:       CirctFirtoolFirtoolOptions,
    module:        MlirModule,
    inputFilename: String
  ): MlirLogicalResult = MlirLogicalResult(
    CAPI.circtFirtoolPopulateCHIRRTLToLowFIRRTL(arena, pm.get, options.get, newString(inputFilename).get)
  )

  def circtFirtoolPopulateLowFIRRTLToHW(pm: MlirPassManager, options: CirctFirtoolFirtoolOptions): MlirLogicalResult =
    MlirLogicalResult(
      CAPI.circtFirtoolPopulateLowFIRRTLToHW(arena, pm.get, options.get)
    )

  def circtFirtoolPopulateHWToSV(pm: MlirPassManager, options: CirctFirtoolFirtoolOptions): MlirLogicalResult =
    MlirLogicalResult(
      CAPI.circtFirtoolPopulateHWToSV(arena, pm.get, options.get)
    )

  def circtFirtoolPopulateExportVerilog(
    pm:       MlirPassManager,
    options:  CirctFirtoolFirtoolOptions,
    callback: String => Unit
  ): MlirLogicalResult = MlirLogicalResult(
    CAPI.circtFirtoolPopulateExportVerilog(arena, pm.get, options.get, newStringCallback(callback).get, NULL)
  )

  def circtFirtoolPopulateExportSplitVerilog(
    pm:        MlirPassManager,
    options:   CirctFirtoolFirtoolOptions,
    directory: String
  ): MlirLogicalResult = MlirLogicalResult(
    CAPI.circtFirtoolPopulateExportSplitVerilog(arena, pm.get, options.get, newString(directory).get)
  )

  def circtFirtoolPopulateFinalizeIR(pm: MlirPassManager, options: CirctFirtoolFirtoolOptions): MlirLogicalResult =
    MlirLogicalResult(CAPI.circtFirtoolPopulateFinalizeIR(arena, pm.get, options.get))

  def mlirLogicalResultIsSuccess(res: MlirLogicalResult): Boolean = circt.MlirLogicalResult.value$get(res.get) != 0

  def mlirLogicalResultIsFailure(res: MlirLogicalResult): Boolean = circt.MlirLogicalResult.value$get(res.get) == 0

  def firrtlTypeGetUInt(width: Int): MlirType = MlirType(CAPI.firrtlTypeGetUInt(arena, mlirCtx, width))

  def firrtlTypeGetSInt(width: Int): MlirType = MlirType(CAPI.firrtlTypeGetSInt(arena, mlirCtx, width))

  def firrtlTypeGetClock(): MlirType = MlirType(CAPI.firrtlTypeGetClock(arena, mlirCtx))

  def firrtlTypeGetReset(): MlirType = MlirType(CAPI.firrtlTypeGetReset(arena, mlirCtx))

  def firrtlTypeGetAsyncReset(): MlirType = MlirType(CAPI.firrtlTypeGetAsyncReset(arena, mlirCtx))

  def firrtlTypeGetAnalog(width: Int): MlirType = MlirType(CAPI.firrtlTypeGetAnalog(arena, mlirCtx, width))

  def firrtlTypeGetVector(element: MlirType, count: Long): MlirType = MlirType(
    CAPI.firrtlTypeGetVector(arena, mlirCtx, element.get, count)
  )

  def firrtlTypeGetBundle(fields: Seq[FIRRTLBundleField]): MlirType =
    val buffer = circt.FIRRTLBundleField.allocateArray(fields.length, arena)
    fields.zipWithIndex.foreach:
      case (field, i) =>
        val fieldBuffer = buffer.asSlice(circt.FIRRTLBundleField.sizeof() * i, circt.FIRRTLBundleField.sizeof())
        circt.FIRRTLBundleField.name$slice(fieldBuffer).copyFrom(mlirIdentifierGet(field.name).get)
        circt.FIRRTLBundleField.isFlip$set(fieldBuffer, field.isFlip)
        circt.FIRRTLBundleField.type$slice(fieldBuffer).copyFrom(field.tpe.get)

    MlirType(CAPI.firrtlTypeGetBundle(arena, mlirCtx, fields.length, buffer))

  def firrtlTypeIsAOpenBundle(tpe: MlirType): Boolean = CAPI.firrtlTypeIsAOpenBundle(tpe.get)

  def firrtlTypeGetBundleFieldIndex(tpe: MlirType, fieldName: String): Int =
    CAPI.firrtlTypeGetBundleFieldIndex(tpe.get, newString(fieldName).get)

  def firrtlTypeGetRef(target: MlirType, forceable: Boolean): MlirType = MlirType(
    CAPI.firrtlTypeGetRef(arena, target.get, forceable)
  )

  def firrtlTypeGetAnyRef(): MlirType = MlirType(CAPI.firrtlTypeGetAnyRef(arena, mlirCtx))

  def firrtlTypeGetInteger(): MlirType = MlirType(CAPI.firrtlTypeGetInteger(arena, mlirCtx))

  def firrtlTypeGetDouble(): MlirType = MlirType(CAPI.firrtlTypeGetDouble(arena, mlirCtx))

  def firrtlTypeGetString(): MlirType = MlirType(CAPI.firrtlTypeGetString(arena, mlirCtx))

  def firrtlTypeGetBoolean(): MlirType = MlirType(CAPI.firrtlTypeGetBoolean(arena, mlirCtx))

  def firrtlTypeGetPath(): MlirType = MlirType(CAPI.firrtlTypeGetPath(arena, mlirCtx))

  def firrtlTypeGetList(elementType: MlirType): MlirType = MlirType(
    CAPI.firrtlTypeGetList(arena, mlirCtx, elementType.get)
  )

  def firrtlTypeGetClass(name: MlirAttribute /* FlatSymbolRefAttr */, elements: Seq[FIRRTLClassElement]): MlirType =
    val buffer = circt.FIRRTLClassElement.allocateArray(elements.length, arena)
    elements.zipWithIndex.foreach:
      case (element, i) =>
        val elementBuffer = buffer.asSlice(circt.FIRRTLClassElement.sizeof() * i, circt.FIRRTLClassElement.sizeof())
        circt.FIRRTLClassElement.name$slice(elementBuffer).copyFrom(mlirIdentifierGet(element.name).get)
        circt.FIRRTLClassElement.type$slice(elementBuffer).copyFrom(element.tpe.get)
        circt.FIRRTLClassElement.direction$set(elementBuffer, element.direction.get)

    MlirType(CAPI.firrtlTypeGetClass(arena, mlirCtx, name.get, elements.length, buffer))

  def firrtlTypeGetMaskType(tpe: MlirType): MlirType = MlirType(CAPI.firrtlTypeGetMaskType(arena, tpe.get))

  def firrtlAttrGetPortDirs(dirs: Seq[FIRRTLDirection]): MlirAttribute =
    val (ptr, length) = seqToArray(dirs)
    MlirAttribute(CAPI.firrtlAttrGetPortDirs(arena, mlirCtx, length, ptr))

  def firrtlAttrGetParamDecl(name: String, tpe: MlirType, value: MlirAttribute): MlirAttribute = MlirAttribute(
    CAPI.firrtlAttrGetParamDecl(arena, mlirCtx, mlirIdentifierGet(name).get, tpe.get, value.get)
  )

  def firrtlAttrGetConvention(convention: FIRRTLConvention): MlirAttribute = MlirAttribute(
    CAPI.firrtlAttrGetConvention(arena, mlirCtx, convention.value)
  )

  def firrtlAttrGetNameKind(nameKind: FIRRTLNameKind): MlirAttribute = MlirAttribute(
    CAPI.firrtlAttrGetNameKind(arena, mlirCtx, nameKind.value)
  )

  def firrtlAttrGetRUW(ruw: FIRRTLRUW): MlirAttribute = MlirAttribute(CAPI.firrtlAttrGetRUW(arena, mlirCtx, ruw.value))

  def firrtlAttrGetMemDir(dir: FIRRTLMemDir): MlirAttribute = MlirAttribute(
    CAPI.firrtlAttrGetMemDir(arena, mlirCtx, dir.value)
  )

  def firrtlAttrGetIntegerFromString(tpe: MlirType, numBits: Int, str: String, radix: Byte): MlirAttribute =
    MlirAttribute(
      CAPI.firrtlAttrGetIntegerFromString(arena, tpe.get, numBits, newString(str).get, radix)
    )

  def firrtlValueFoldFlow(value: MlirValue, flow: Int): Int = CAPI.firrtlValueFoldFlow(value.get, flow)

  def firrtlImportAnnotationsFromJSONRaw(annotationsStr: String): Option[MlirAttribute] =
    val attr   = circt.MlirAttribute.allocate(arena)
    val result = CAPI.firrtlImportAnnotationsFromJSONRaw(mlirCtx, newString(annotationsStr).get, attr)
    if (result)
      Some(MlirAttribute(attr))
    else
      None

  def chirrtlTypeGetCMemory(elementType: MlirType, numElements: Long): MlirType = MlirType(
    CAPI.chirrtlTypeGetCMemory(arena, mlirCtx, elementType.get, numElements)
  )

  def chirrtlTypeGetCMemoryPort(): MlirType = MlirType(CAPI.chirrtlTypeGetCMemoryPort(arena, mlirCtx))

  def hwInnerRefAttrGet(moduleName: String, innerSym: String): MlirAttribute =
    MlirAttribute(CAPI.hwInnerRefAttrGet(arena, mlirStringAttrGet(moduleName).get, mlirStringAttrGet(innerSym).get))

  def hwInnerSymAttrGet(symName: String): MlirAttribute =
    MlirAttribute(CAPI.hwInnerSymAttrGet(arena, mlirStringAttrGet(symName).get))

  def hwInnerSymAttrGetEmpty(): MlirAttribute = MlirAttribute(CAPI.hwInnerSymAttrGetEmpty(arena, mlirCtx))

  def hwInstanceGraphGet(operation: MlirOperation): HWInstanceGraph = HWInstanceGraph(
    CAPI.hwInstanceGraphGet(arena, operation.get)
  )

  def hwInstanceGraphGetTopLevelNode(instanceGraph: HWInstanceGraph): HWInstanceGraphNode = HWInstanceGraphNode(
    CAPI.hwInstanceGraphGetTopLevelNode(arena, instanceGraph.get)
  )

  def hwInstanceGraphForEachNode(instaceGraph: HWInstanceGraph, callback: HWInstanceGraphNode => Unit): Any =
    val cb = HWInstanceGraphNodeCallback(
      circt.HWInstanceGraphNodeCallback.allocate(
        new circt.HWInstanceGraphNodeCallback:
          def apply(node: MemorySegment, userData: MemorySegment): Unit =
            callback(HWInstanceGraphNode(node))
        ,
        arena
      )
    )
    CAPI.hwInstanceGraphForEachNode(instaceGraph.get, cb.get, NULL)

  def hwInstanceGraphNodeEqual(lhs: HWInstanceGraphNode, rhs: HWInstanceGraphNode): Any =
    CAPI.hwInstanceGraphNodeEqual(lhs.get, rhs.get)

  def hwInstanceGraphNodeGetModuleOp(node: HWInstanceGraphNode): MlirOperation = MlirOperation(
    CAPI.hwInstanceGraphNodeGetModuleOp(arena, node.get)
  )

  //
  // OM C-API
  //

  def omTypeIsAClassType(tpe:          MlirType):   Boolean        = CAPI.omTypeIsAClassType(tpe.get)
  def omClassTypeGetName(tpe:          MlirType):   MlirIdentifier = MlirIdentifier(CAPI.omClassTypeGetName(arena, tpe.get))
  def omTypeIsAFrozenBasePathType(tpe: MlirType):   Boolean        = CAPI.omTypeIsAFrozenBasePathType(tpe.get)
  def omTypeIsAFrozenPathType(tpe:     MlirType):   Boolean        = CAPI.omTypeIsAFrozenPathType(tpe.get)
  def omTypeIsAMapType(tpe:            MlirType):   Boolean        = CAPI.omTypeIsAMapType(tpe.get)
  def omMapTypeGetKeyType(tpe:         MlirType):   MlirType       = MlirType(CAPI.omMapTypeGetKeyType(arena, tpe.get))
  def omTypeIsAStringType(tpe:         MlirType):   Boolean        = CAPI.omTypeIsAStringType(tpe.get)
  def omEvaluatorNew(mod:              MlirModule): OMEvaluator    = OMEvaluator(CAPI.omEvaluatorNew(arena, mod.get))
  def omEvaluatorInstantiate(evaluator: OMEvaluator, className: String, actualParams: Seq[OMEvaluatorValue])
    : OMEvaluatorValue =
    val params = seqToArray(actualParams)
    OMEvaluatorValue(
      CAPI.omEvaluatorInstantiate(arena, evaluator.get, mlirStringAttrGet(className).get, params._2, params._1)
    )

  def omEvaluatorGetModule(evaluator: OMEvaluator): MlirModule = MlirModule(
    CAPI.omEvaluatorGetModule(arena, evaluator.get)
  )
  def omEvaluatorObjectIsNull(obj: OMEvaluatorValue): Boolean = CAPI.omEvaluatorObjectIsNull(obj.get)
  def omEvaluatorObjectGetType(obj: OMEvaluatorValue):                MlirType         = MlirType(
    CAPI.omEvaluatorObjectGetType(arena, obj.get)
  )
  def omEvaluatorObjectGetField(obj: OMEvaluatorValue, name: String): OMEvaluatorValue = OMEvaluatorValue(
    CAPI.omEvaluatorObjectGetField(arena, obj.get, mlirStringAttrGet(name).get)
  )
  def omEvaluatorObjectGetHash(obj: OMEvaluatorValue): Int = CAPI.omEvaluatorObjectGetHash(obj.get)
  def omEvaluatorObjectIsEq(obj: OMEvaluatorValue, other: OMEvaluatorValue):           Boolean          =
    CAPI.omEvaluatorObjectIsEq(obj.get, other.get)
  def omEvaluatorObjectGetFieldNames(obj: OMEvaluatorValue):                           MlirAttribute    = MlirAttribute(
    CAPI.omEvaluatorObjectGetFieldNames(arena, obj.get)
  )
  def omEvaluatorValueGetLoc(evaluatorValue: OMEvaluatorValue):                        MlirLocation     = MlirLocation(
    CAPI.omEvaluatorValueGetLoc(arena, evaluatorValue.get)
  )
  def omEvaluatorValueIsNull(evaluatorValue: OMEvaluatorValue):                        Boolean          =
    CAPI.omEvaluatorValueIsNull(evaluatorValue.get)
  def omEvaluatorValueIsAObject(evaluatorValue: OMEvaluatorValue):                     Boolean          =
    CAPI.omEvaluatorValueIsAObject(evaluatorValue.get)
  def omEvaluatorValueIsAPrimitive(evaluatorValue: OMEvaluatorValue):                  Boolean          =
    CAPI.omEvaluatorValueIsAPrimitive(evaluatorValue.get)
  def omEvaluatorValueGetPrimitive(evaluatorValue: OMEvaluatorValue):                  MlirAttribute    = MlirAttribute(
    CAPI.omEvaluatorValueGetPrimitive(arena, evaluatorValue.get)
  )
  def omEvaluatorValueFromPrimitive(primitive: MlirAttribute):                         OMEvaluatorValue = OMEvaluatorValue(
    CAPI.omEvaluatorValueFromPrimitive(arena, primitive.get)
  )
  def omEvaluatorValueIsAList(evaluatorValue: OMEvaluatorValue):                       Boolean          =
    CAPI.omEvaluatorValueIsAList(evaluatorValue.get)
  def omEvaluatorListGetNumElements(evaluatorValue: OMEvaluatorValue):                 Long             =
    CAPI.omEvaluatorListGetNumElements(evaluatorValue.get)
  def omEvaluatorListGetElement(evaluatorValue: OMEvaluatorValue, pos: Long):          OMEvaluatorValue = OMEvaluatorValue(
    CAPI.omEvaluatorListGetElement(arena, evaluatorValue.get, pos)
  )
  def omEvaluatorValueIsATuple(evaluatorValue: OMEvaluatorValue):                      Boolean          =
    CAPI.omEvaluatorValueIsATuple(evaluatorValue.get)
  def omEvaluatorTupleGetNumElements(evaluatorValue: OMEvaluatorValue):                Long             =
    CAPI.omEvaluatorTupleGetNumElements(evaluatorValue.get)
  def omEvaluatorTupleGetElement(evaluatorValue: OMEvaluatorValue, pos: Long):         OMEvaluatorValue = OMEvaluatorValue(
    CAPI.omEvaluatorTupleGetElement(arena, evaluatorValue.get, pos)
  )
  def omEvaluatorMapGetElement(evaluatorValue: OMEvaluatorValue, attr: MlirAttribute): OMEvaluatorValue =
    OMEvaluatorValue(
      CAPI.omEvaluatorMapGetElement(arena, evaluatorValue.get, attr.get)
    )
  def omEvaluatorMapGetKeys(obj: OMEvaluatorValue):                                    MlirAttribute    = MlirAttribute(
    CAPI.omEvaluatorMapGetKeys(arena, obj.get)
  )
  def omEvaluatorValueIsAMap(evaluatorValue: OMEvaluatorValue):                        Boolean          =
    CAPI.omEvaluatorValueIsAMap(evaluatorValue.get)
  def omEvaluatorMapGetType(evaluatorValue: OMEvaluatorValue):                         MlirType         = MlirType(
    CAPI.omEvaluatorMapGetType(arena, evaluatorValue.get)
  )
  def omEvaluatorValueIsABasePath(evaluatorValue: OMEvaluatorValue):                   Boolean          =
    CAPI.omEvaluatorValueIsABasePath(evaluatorValue.get)
  def omEvaluatorBasePathGetEmpty():                                                   OMEvaluatorValue = OMEvaluatorValue(
    CAPI.omEvaluatorBasePathGetEmpty(arena, mlirCtx)
  )
  def omEvaluatorValueIsAPath(evaluatorValue: OMEvaluatorValue):                       Boolean          =
    CAPI.omEvaluatorValueIsAPath(evaluatorValue.get)
  def omEvaluatorPathGetAsString(evaluatorValue: OMEvaluatorValue):                    String           = mlirStringAttrGetValue(
    MlirAttribute(CAPI.omEvaluatorPathGetAsString(arena, evaluatorValue.get))
  )
  def omEvaluatorValueIsAReference(evaluatorValue: OMEvaluatorValue):                  Boolean          =
    CAPI.omEvaluatorValueIsAReference(evaluatorValue.get)
  def omEvaluatorValueGetReferenceValue(evaluatorValue: OMEvaluatorValue):             OMEvaluatorValue =
    OMEvaluatorValue(CAPI.omEvaluatorValueGetReferenceValue(arena, evaluatorValue.get))
  def omAttrIsAReferenceAttr(attr: MlirAttribute): Boolean = CAPI.omAttrIsAReferenceAttr(attr.get)
  def omReferenceAttrGetInnerRef(attr: MlirAttribute): MlirAttribute = MlirAttribute(
    CAPI.omReferenceAttrGetInnerRef(arena, attr.get)
  )
  def omAttrIsAIntegerAttr(attr:     MlirAttribute): Boolean       = CAPI.omAttrIsAIntegerAttr(attr.get)
  def omIntegerAttrGetInt(attr:      MlirAttribute): MlirAttribute = MlirAttribute(CAPI.omIntegerAttrGetInt(arena, attr.get))
  def omIntegerAttrGet(attr:         MlirAttribute): MlirAttribute = MlirAttribute(CAPI.omIntegerAttrGet(arena, attr.get))
  def omAttrIsAListAttr(attr:        MlirAttribute): Boolean       = CAPI.omAttrIsAListAttr(attr.get)
  def omListAttrGetNumElements(attr: MlirAttribute): Long          = CAPI.omListAttrGetNumElements(attr.get)
  def omListAttrGetElement(attr: MlirAttribute, pos: Long): MlirAttribute = MlirAttribute(
    CAPI.omListAttrGetElement(arena, attr.get, pos)
  )
  def omAttrIsAMapAttr(attr:        MlirAttribute): Boolean = CAPI.omAttrIsAMapAttr(attr.get)
  def omMapAttrGetNumElements(attr: MlirAttribute): Long    = CAPI.omMapAttrGetNumElements(attr.get)
  def omMapAttrGetElementKey(attr: MlirAttribute, pos: Long):   MlirIdentifier = MlirIdentifier(
    CAPI.omMapAttrGetElementKey(arena, attr.get, pos)
  )
  def omMapAttrGetElementValue(attr: MlirAttribute, pos: Long): MlirAttribute  = MlirAttribute(
    CAPI.omMapAttrGetElementValue(arena, attr.get, pos)
  )
