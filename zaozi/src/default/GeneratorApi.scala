// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
package me.jiuyang.zaozi.default

import scala.util.Try

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.magic.validateCircuit
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

import org.llvm.circt.scalalib.capi.dialect.emit.given_DialectApi as EmitDialectApi
import org.llvm.circt.scalalib.capi.dialect.firrtl.{
  given_DialectApi,
  given_FirrtlBundleFieldApi,
  given_FirrtlDirectionApi,
  given_TypeApi,
  DialectApi as FirrtlDialectApi,
  FirrtlConvention,
  FirrtlNameKind
}
import org.llvm.circt.scalalib.dialect.firrtl.operation.given
import org.llvm.circt.scalalib.dialect.firrtl.operation.{
  given_CircuitApi,
  given_ModuleApi,
  Circuit,
  CircuitApi,
  ConnectApi,
  InstanceApi,
  Module as CirctModule,
  ModuleApi,
  OpenSubfieldApi,
  RefDefineApi,
  SubfieldApi,
  WireApi
}
import org.llvm.circt.scalalib.capi.dialect.sv.given_DialectApi as SvDialectApi
import org.llvm.mlir.scalalib.capi.ir.{
  given_AttributeApi,
  given_BlockApi,
  given_ContextApi,
  given_IdentifierApi,
  given_LocationApi,
  given_ModuleApi,
  given_NamedAttributeApi,
  given_OperationApi,
  given_RegionApi,
  given_TypeApi,
  given_ValueApi,
  Block,
  Context,
  ContextApi,
  LocationApi,
  Module as MlirModule,
  ModuleApi as MlirModuleApi,
  NamedAttributeApi,
  Operation,
  OperationApi,
  Type
}
import org.llvm.mlir.scalalib.capi.pass.{given_PassManagerApi, PassManager}

import java.lang.foreign.Arena
import java.nio.file.StandardOpenOption.*

export given_GeneratorApi.*
export me.jiuyang.zaozi.magic.macros.generator

given GeneratorApi with
  extension [PARAM <: Parameter, L <: LayerInterface[PARAM], I <: HWInterface[PARAM], P <: DVInterface[PARAM, L]](
    generator: Generator[PARAM, L, I, P]
  )
    def module(
      parameter: PARAM
    )(
      using Arena,
      Context
    ): CirctModule =
      val io                = generator.interface(parameter)
      val probe             = generator.probe(parameter)
      val unknownLocation   = summon[LocationApi].locationUnknownGet
      val ioNumFields       = io.toMlirType.getBundleNumFields.toInt
      val probeNumFields    = probe.toMlirType.getBundleNumFields.toInt
      val bfs               =
        Seq.tabulate(ioNumFields)(io.toMlirType.getBundleFieldByIndex) ++
          Seq.tabulate(probeNumFields)(probe.toMlirType.getBundleFieldByIndex)
      given Seq[LayerTree]  = generator.layers(parameter).flatMap(_._dfs)
      val module            = summon[ModuleApi].op(
        generator.moduleName(parameter),
        unknownLocation,
        FirrtlConvention.Scalarized,
        bfs.map(i => (i, unknownLocation)), // TODO: record location for Bundle?
        summon[Seq[LayerTree]].filter(_._children.isEmpty).map(_._hierarchy.map(_._name))
      )
      given Block           = module.block
      val ioWire            = summon[WireApi].op(
        "io",
        summon[LocationApi].locationUnknownGet,
        FirrtlNameKind.Droppable,
        io.toMlirType
      )
      ioWire.operation.appendToBlock()
      val probeWire         = summon[WireApi].op(
        "probe",
        summon[LocationApi].locationUnknownGet,
        FirrtlNameKind.Droppable,
        probe.toMlirType
      )
      probeWire.operation.appendToBlock()
      Seq
        .tabulate(ioNumFields): ioIdx =>
          (bfs(ioIdx), ioIdx)
        .foreach:
          case (bf, idx) =>
            val subRefToIOWire = summon[SubfieldApi].op(
              ioWire.result,
              idx,
              unknownLocation
            )
            subRefToIOWire.operation.appendToBlock()
            (
              if (bf.getIsFlip)
                summon[ConnectApi].op(module.getIO(idx), subRefToIOWire.result, unknownLocation)
              else
                summon[ConnectApi].op(subRefToIOWire.result, module.getIO(idx), unknownLocation)
            ).operation.appendToBlock()
      Seq
        .tabulate(probeNumFields): probeIdx =>
          (bfs(ioNumFields + probeIdx), probeIdx)
        .foreach:
          case (bf, idx) =>
            val subRefToProbeWire = summon[OpenSubfieldApi].op(
              probeWire.result,
              idx,
              unknownLocation
            )
            subRefToProbeWire.operation.appendToBlock()
            summon[RefDefineApi]
              .op(module.getIO(ioNumFields + idx), subRefToProbeWire.result, unknownLocation)
              .operation
              .appendToBlock()
      given Interface[I]    =
        new Interface[I]:
          val _tpe:       I         = io
          val _operation: Operation = ioWire.operation
      given Interface[P]    =
        new Interface[P]:
          val _tpe:       P         = probe
          val _operation: Operation = probeWire.operation
      given InstanceContext = new InstanceContext
      generator.architecture(parameter)
      module

    def instance(
      parameter: PARAM
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Instance[I, P] =
      val ioTpe       = generator.interface(parameter)
      val probeTpe    = generator.probe(parameter)
      val ioFields    = Seq.tabulate(ioTpe.toMlirType.getBundleNumFields.toInt)(ioTpe.toMlirType.getBundleFieldByIndex)
      val probeFields =
        Seq.tabulate(probeTpe.toMlirType.getBundleNumFields.toInt)(probeTpe.toMlirType.getBundleFieldByIndex)
      // TODO: add layer symbol here? rather than from top to down searching?
      val instanceOp  = summon[InstanceApi].op(
        moduleName = generator.moduleName(parameter),
        instanceName = valName,
        nameKind = FirrtlNameKind.Interesting,
        location = locate,
        interface = ioFields ++ probeFields
      )
      instanceOp.operation.appendToBlock()
      val ioWire      = summon[WireApi].op(
        s"${valName}_io",
        summon[LocationApi].locationUnknownGet,
        FirrtlNameKind.Droppable,
        ioTpe.toMlirType
      )
      ioWire.operation.appendToBlock()
      val probeWire   = summon[WireApi].op(
        s"${valName}_probe",
        summon[LocationApi].locationUnknownGet,
        FirrtlNameKind.Droppable,
        probeTpe.toMlirType
      )
      probeWire.operation.appendToBlock()

      ioFields.zipWithIndex.foreach:    (field, idx) =>
        val flip       = field.getIsFlip
        val instanceIO = instanceOp.operation.getResult(idx)
        val wireIO     = summon[SubfieldApi].op(
          ioWire.result,
          idx,
          locate
        )
        wireIO.operation.appendToBlock()
        val connect    =
          if (flip) summon[ConnectApi].op(wireIO.result, instanceIO, locate)
          else summon[ConnectApi].op(instanceIO, wireIO.result, locate)
        connect.operation.appendToBlock()
      probeFields.zipWithIndex.foreach: (field, idx) =>
        val instanceIO = instanceOp.operation.getResult(ioFields.length + idx)
        val wireProbe  = summon[OpenSubfieldApi].op(
          probeWire.result,
          idx,
          locate
        )
        wireProbe.operation.appendToBlock()
        val connect    = summon[RefDefineApi].op(wireProbe.result, instanceIO, locate)
        connect.operation.appendToBlock()

      new Instance[I, P]:
        val _ioTpe     = ioTpe
        val _probeTpe  = probeTpe
        val _operation = instanceOp.operation
        val _ioWire    = new Wire[I]:
          private[zaozi] val _tpe       = ioTpe
          private[zaozi] val _operation = ioWire.operation
        val _probeWire = new Wire[P]:
          private[zaozi] val _tpe       = probeTpe
          private[zaozi] val _operation = probeWire.operation

    def dumpMlirbc(
      parameter: PARAM
    )(
      using Arena,
      Context
    ): Unit =
      val mlirbcFile =
        os.Path(
          sys.env.getOrElse("ZAOZI_OUTDIR", ""),
          os.pwd
        ) / s"${generator.moduleName(parameter)}.mlirbc"

      generator.elaborationCache.get(parameter) match
        case Some(mlirbc) =>
          os.write.over(mlirbcFile, mlirbc)
        case None         =>
          given MlirModule = summon[MlirModuleApi].moduleCreateEmpty(summon[LocationApi].locationUnknownGet)
          given Circuit    = summon[CircuitApi].op(generator.moduleName(parameter))
          summon[Circuit].appendToModule()
          generator.module(parameter).appendToCircuit()
          validateCircuit()

          val out = os.write.outputStream(mlirbcFile, openOptions = Seq(WRITE, CREATE, TRUNCATE_EXISTING))
          summon[MlirModule].getOperation.writeBytecode(bc => out.write(bc))
          generator.elaborationCache.put(parameter, os.read.bytes(mlirbcFile))

    def instantiate(
      parameter: PARAM
    )(
      using Arena,
      Context,
      Block,
      sourcecode.File,
      sourcecode.Line,
      sourcecode.Name.Machine,
      InstanceContext
    ): Instance[I, P] =
      generator.dumpMlirbc(parameter)
      generator.instance(parameter)

    private def configImpl(
      parameter:  PARAM,
      configFile: os.Path
    )(
      using upickle.default.Writer[PARAM]
    ) = os.write.over(configFile, upickle.default.write(parameter))

    private def designImpl(
      configFile: os.Path
    )(
      using upickle.default.Reader[PARAM]
    ) =
      given Arena   = Arena.ofConfined()
      given Context = summon[ContextApi].contextCreate
      summon[FirrtlDialectApi].loadDialect

      generator.dumpMlirbc(upickle.default.read(os.read(configFile)))

      summon[Context].destroy()
      summon[Arena].close()

    def mainImpl(
      args: Array[String]
    )(
      using upickle.default.ReadWriter[PARAM]
    ): Unit =
      args.toList match
        case subcmd :: configPath :: tail if Try(os.Path(configPath, os.pwd)).isSuccess =>
          val configFile = os.Path(configPath, os.pwd)
          subcmd match
            case "config" => configImpl(generator.parseParameter(tail), configFile)
            case "design" => designImpl(configFile)
        case _                                                                          =>
          println("Need to specify a sub command and provide a config path: config/design <path>")
          sys.exit(1)

end given
