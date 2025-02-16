// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>
import mill._
import mill.scalalib.TestModule.Utest
import mill.scalalib._
import mill.scalalib.scalafmt._
import $ivy.`com.lihaoyi::mill-contrib-jmh:`
import contrib.jmh.JmhModule
import os.Path

object v {
  val scala      = "3.6.2"
  val mainargs   = ivy"com.lihaoyi::mainargs:0.7.6"
  val oslib      = ivy"com.lihaoyi::os-lib:0.11.3"
  val upickle    = ivy"com.lihaoyi::upickle:4.0.2"
  val utest      = ivy"com.lihaoyi::utest:0.8.4"
  val sourcecode = ivy"com.lihaoyi::sourcecode:0.4.2"
  val pprint     = ivy"com.lihaoyi::pprint:0.9.0"
  val jmh        = "1.35"
}

object zaozi extends ScalaModule with ScalafmtModule { m =>
  def scalaVersion = T(v.scala)
  def ivyDeps      = T(Seq(v.mainargs, v.oslib, v.upickle, v.sourcecode))
  def moduleDeps   = Seq(circtlib)

  override def scalacOptions: Target[Seq[String]] = T(super.scalacOptions() ++ Some("-Xprint-suspension"))

  object lit extends ScalaModule with ScalafmtModule {
    def scalaVersion = T(v.scala)
    def moduleDeps   = Seq(m)
    override def forkArgs: T[Seq[String]] = T(
      super.forkArgs() ++ circtlib.forkArgs()
    )
    object tests extends LitModule {
      def scalaVersion:    T[String]       = T(m.scalaVersion())
      def runClasspath:    T[Seq[os.Path]] = T(lit.runClasspath().map(_.path))
      def javaLibraryPath: T[Seq[os.Path]] = T(
        (circtlib.libraryPaths()).map(_.path)
      )
      def javaHome:        T[os.Path]      = T(os.Path(sys.props("java.home")))
      def litDir:          T[os.Path]      = T(millSourcePath)
      def litConfigIn:     T[PathRef]      = T.source(millSourcePath / "lit.site.cfg.py.in")
    }
  }

  object benchmark extends ScalaModule with JmhModule {
    def scalaVersion   = T(v.scala)
    def moduleDeps     = Seq(tests)
    def jmhCoreVersion = T(v.jmh)
    def forkArgs: T[Seq[String]] = T(
      super.forkArgs() ++ circtlib.forkArgs()
    )
    def runJmh(args: String*) =
      T.command {
        val (_, resources) = generateBenchmarkSources()
        mill.util.Jvm.runSubprocess(
          "org.openjdk.jmh.Main",
          classPath = (runClasspath() ++ generatorDeps()).map(_.path) ++
            Seq(compileGeneratedSources().path, resources),
          mainArgs = args,
          workingDir = T.ctx().dest,
          jvmArgs = forkArgs()
        )
      }
  }

  object tests extends ScalaTests with ScalafmtModule with Utest {
    def ivyDeps = Agg(v.utest)

    override def forkArgs: T[Seq[String]] = T(
      super.forkArgs() ++ circtlib.forkArgs()
    )
  }
}

// The Scala API
object circtlib extends ScalaModule with ScalafmtModule with PanamaModule { outer =>
  def scalaVersion = T(v.scala)

  override def dumpIncludes() = T.command {
    super.dumpIncludes()()
    includeFiles().foreach { file =>
      val lines =
        os.read
          .lines(file)
          .filter(str => str.contains(circtInstallPath().toString))
          .map(_.replaceAll(circtInstallPath().toString, "\\$CIRCT_INSTALL_PATH").trim)
      os.write.over(file, (license ++ lines).mkString("\n"))
    }
  }

  def includeConstantsFile = millSourcePath / "capi" / "includeConstants.txt"

  def includeFunctionsFile = millSourcePath / "capi" / "includeFunctions.txt"

  def includeStructsFile = millSourcePath / "capi" / "includeStructs.txt"

  def includeTypedefsFile = millSourcePath / "capi" / "includeTypedefs.txt"

  def includeUnionsFile = millSourcePath / "capi" / "includeUnions.txt"

  def includeVarsFile = millSourcePath / "capi" / "includeVars.txt"

  def linkLibrariesFile = millSourcePath / "capi" / "linkLibraries.txt"

  def target = T("org.llvm.circt")

  def headerClassName = T("CAPI")

  def header = T(PathRef(millSourcePath / "capi" / "jextract-headers.h"))

  def circtInstallPath = T(
    os.Path(T.env.getOrElse("CIRCT_INSTALL_PATH", "CIRCT_INSTALL_PATH not found, you are not in the nix env?"))
  )

  def jextractBinary = T(
    os.Path(
      T.env.getOrElse("JEXTRACT_INSTALL_PATH", "JEXTRACT_INSTALL_PATH not found, you are not in the nix env?")
    ) / "bin" / "jextract"
  )

  def includePaths = T(Seq(mlirlib.mlirInstallPath() / "include", circtInstallPath() / "include").map(PathRef(_)))

  def libraryPaths = T(Seq(mlirlib.mlirInstallPath() / "lib", circtInstallPath() / "lib").map(PathRef(_)))

  override def moduleDeps = Seq(mlirlib)

  def ivyDeps = Agg(v.pprint)

  object tests extends ScalaModule with ScalafmtModule with Utest {
    override def forkArgs: T[Seq[String]] = T(outer.forkArgs)

    override def moduleDeps = Seq(circtlib, mlirlib)

    def ivyDeps = Agg(v.utest)

    override def scalaVersion = outer.scalaVersion
  }
}

object mlirlib extends ScalaModule with ScalafmtModule with PanamaModule {
  def scalaVersion = T(v.scala)

  override def dumpIncludes() = T.command {
    super.dumpIncludes()()
    includeFiles().foreach { file =>
      val lines =
        os.read
          .lines(file)
          .filter(str => str.contains(mlirInstallPath().toString))
          // to eliminte error cause by a jextract bug
          .filter(str => !str.contains("mlirTypeIDAllocatorAllocateTypeID"))
          .map(_.replaceAll(mlirInstallPath().toString, "\\$MLIR_INSTALL_PATH").trim)
      os.write.over(file, (license ++ lines).mkString("\n"))
    }
  }

  def includeConstantsFile = millSourcePath / "capi" / "includeConstants.txt"

  def includeFunctionsFile = millSourcePath / "capi" / "includeFunctions.txt"

  def includeStructsFile = millSourcePath / "capi" / "includeStructs.txt"

  def includeTypedefsFile = millSourcePath / "capi" / "includeTypedefs.txt"

  def includeUnionsFile = millSourcePath / "capi" / "includeUnions.txt"

  def includeVarsFile = millSourcePath / "capi" / "includeVars.txt"

  def linkLibrariesFile = millSourcePath / "capi" / "linkLibraries.txt"

  def target = T("org.llvm.mlir")

  def headerClassName = T("CAPI")

  def header = T(PathRef(millSourcePath / "capi" / "jextract-headers.h"))

  def mlirInstallPath = T.input(
    os.Path(T.env.getOrElse("MLIR_INSTALL_PATH", "MLIR_INSTALL_PATH not found, you are not in the nix env?"))
  )

  def jextractBinary = T(
    os.Path(
      T.env.getOrElse("JEXTRACT_INSTALL_PATH", "JEXTRACT_INSTALL_PATH not found, you are not in the nix env?")
    ) / "bin" / "jextract"
  )

  def includePaths = T(Seq(PathRef(mlirInstallPath() / "include")))

  def libraryPaths = T(Seq(PathRef(mlirInstallPath() / "lib")))

  object tests extends ScalaTests with ScalafmtModule with Utest {
    def ivyDeps = Agg(v.utest)

    override def forkArgs: T[Seq[String]] = T(
      super.forkArgs() ++ Seq("--enable-native-access=ALL-UNNAMED", "--enable-preview")
        ++ libraryPaths().map(p => s"-Djava.library.path=${p.path}")
    )
  }
}

// Lit-based Test
trait LitModule extends Module {
  def scalaVersion:    T[String]
  def runClasspath:    T[Seq[os.Path]]
  def javaLibraryPath: T[Seq[os.Path]]
  def javaHome:        T[os.Path]
  def litDir:          T[os.Path]
  def litConfigIn:     T[PathRef]
  def litConfig:       T[PathRef] = T {
    os.write(
      T.dest / "lit.site.cfg.py",
      os.read(litConfigIn().path)
        .replaceAll("@SCALA_VERSION@", scalaVersion())
        .replaceAll("@RUN_CLASSPATH@", runClasspath().mkString(","))
        .replaceAll("@JAVA_HOME@", javaHome().toString)
        .replaceAll("@JAVA_LIBRARY_PATH@", javaLibraryPath().mkString(","))
        .replaceAll("@LIT_DIR@", litDir().toString)
    )
    PathRef(T.dest)
  }
  def litBinary          = T(
    os.Path(
      T.env.getOrElse("LIT_INSTALL_PATH", "LIT_INSTALL_PATH not found, you are not in the nix env?")
    ) / "bin" / "lit"
  )
  def run(args: String*) = T.command(
    os.proc(litBinary().toString(), litConfig().path, "-a")
      .call(T.dest, stdout = os.ProcessOutput.Readlines(line => T.ctx().log.info("[lit] " + line)))
  )
}

// Panama API
trait PanamaModule extends JavaModule {
  val license = Seq(
    "# SPDX-License-Identifier: Apache-2.0",
    "# SPDX-FileCopyrightText: 2025 Jiuyang Liu <liu@jiuyang.me>",
    ""
  )

  // API to regenerate all C-API from headers
  def dumpIncludes(): Command[Unit] = T.command {
    val f = os.temp()
    os.proc(
      Seq(jextractBinary().toString, header().path.toString)
        ++ includePaths().flatMap(p => Seq("-I", p.path.toString))
        ++ Seq("--dump-includes", f.toString)
    ).call()

    includeFiles().foreach { file =>
      os.remove(file)
      os.write(file, "")
    }

    os.read
      .lines(f)
      .filter(s => s.nonEmpty && !s.startsWith("#"))
      .filter(str => !str.contains("jextract"))
      .foreach { str =>
        val writeStr = str.replaceFirst("--include.+? ", "") + "\n"
        if (str.startsWith("--include-constant")) os.write.append(includeConstantsFile(), writeStr)
        if (str.startsWith("--include-function")) os.write.append(includeFunctionsFile(), writeStr)
        if (str.startsWith("--include-struct")) os.write.append(includeStructsFile(), writeStr)
        if (str.startsWith("--include-typedef")) os.write.append(includeTypedefsFile(), writeStr)
        if (str.startsWith("--include-union")) os.write.append(includeUnionsFile(), writeStr)
        if (str.startsWith("--include-var")) os.write.append(includeVarsFile(), writeStr)
      }
  }

  override def generatedSources: Target[Seq[PathRef]] = T {
    super.generatedSources() ++ {
      // @formatter:off
      os.proc(
        Seq(jextractBinary().toString, header().path.toString)
          ++ includePaths().flatMap(p => Seq("-I", p.path.toString))
          ++ Seq(
          "-t", target(),
          "--header-class-name", headerClassName(),
          "--source",
          "--output", T.dest.toString
        ) ++ includeFunctions().flatMap(f => Seq("--include-function", f)) ++
          includeConstants().flatMap(f => Seq("--include-constant", f)) ++
          includeStructs().flatMap(f => Seq("--include-struct", f)) ++
          includeTypedefs().flatMap(f => Seq("--include-typedef", f)) ++
          includeUnions().flatMap(f => Seq("--include-union", f)) ++
          includeVars().flatMap(f => Seq("--include-var", f)) ++
          linkLibraries().flatMap(l => Seq("-l", l))
      ).call(T.dest)
      // @formatter:on
      Seq(PathRef(T.dest))
    }
  }

  override def javacOptions: Target[Seq[String]] = T(super.javacOptions() ++ Seq("--enable-preview", "--release", "21"))

  override def forkArgs: T[Seq[String]] = T(
    super.forkArgs() ++ Seq("--enable-native-access=ALL-UNNAMED", "--enable-preview")
      ++ Some(s"-Djava.library.path=${libraryPaths().map(_.path).distinct.mkString(":")}")
  )

  def includeFiles = T(
    Seq(
      includeConstantsFile(),
      includeFunctionsFile(),
      includeStructsFile(),
      includeTypedefsFile(),
      includeUnionsFile(),
      includeVarsFile()
    )
  )

  def includeConstantsFile: Target[Path]
  def includeConstants:     Target[IndexedSeq[String]] = T.input(
    os.read.lines(includeConstantsFile()).filter(s => s.nonEmpty && !s.startsWith("#")).map(_.replaceFirst(" .*", ""))
  )

  def includeFunctionsFile: Target[Path]
  def includeFunctions:     Target[IndexedSeq[String]] = T.input(
    os.read.lines(includeFunctionsFile()).filter(s => s.nonEmpty && !s.startsWith("#")).map(_.replaceFirst(" .*", ""))
  )

  def includeStructsFile: Target[Path]
  def includeStructs:     Target[IndexedSeq[String]] = T.input(
    os.read.lines(includeStructsFile()).filter(s => s.nonEmpty && !s.startsWith("#")).map(_.replaceFirst(" .*", ""))
  )

  def includeTypedefsFile: Target[Path]
  def includeTypedefs:     Target[IndexedSeq[String]] = T.input(
    os.read.lines(includeTypedefsFile()).filter(s => s.nonEmpty && !s.startsWith("#")).map(_.replaceFirst(" .*", ""))
  )

  def includeUnionsFile: Target[Path]
  def includeUnions:     Target[IndexedSeq[String]] = T.input(
    os.read.lines(includeUnionsFile()).filter(s => s.nonEmpty && !s.startsWith("#")).map(_.replaceFirst(" .*", ""))
  )

  def includeVarsFile: Target[Path]
  def includeVars:     Target[IndexedSeq[String]] = T.input(
    os.read.lines(includeVarsFile()).filter(s => s.nonEmpty && !s.startsWith("#")).map(_.replaceFirst(" .*", ""))
  )

  def linkLibrariesFile: Target[Path]
  def linkLibraries:     Target[IndexedSeq[String]] = T.input(
    os.read.lines(linkLibrariesFile()).filter(s => s.nonEmpty && !s.startsWith("#")).map(_.replaceFirst(" .*", ""))
  )

  def target: Target[String]

  def headerClassName: Target[String]

  def header: Target[PathRef]

  def includePaths: Target[Seq[PathRef]]

  def libraryPaths: Target[Seq[PathRef]]

  def jextractBinary: Target[Path]
}

object rvdecoderdb extends RVDecoderDB

trait RVDecoderDB extends ScalaModule with ScalafmtModule {
  def millSourcePath = os.pwd / "rvdecoderdb"
  override def sources: T[Seq[PathRef]] = T.sources { super.sources() ++ Some(PathRef(millSourcePath / "src"))  }
  def scalaVersion = T(v.scala)
  def ivyDeps      = T(Seq(v.mainargs, v.oslib, v.upickle))

  object tests extends ScalaTests with ScalafmtModule with Utest {
    def ivyDeps = Agg(v.utest)
  }
}