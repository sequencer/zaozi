# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>

{ lib
, stdenv
, generateIvyCache
, makeWrapper
, mill
, circt-install
, mlir-install
, jextract-21
, lit
, scala-cli
, add-determinism
, mill-ivy-env-shell-hook
}:

let
  self = stdenv.mkDerivation rec {
    name = "zaozi";

    src = with lib.fileset;
      toSource {
        root = ./../..;
        fileset = unions [
          ./../../build.mill
          ./../../circtlib
          ./../../mlirlib
          ./../../zaozi
        ];
      };

    passthru.millDeps = generateIvyCache {
      inherit name;
      src = self.src;
      hash = "sha256-S5mmXOyUJMuJj4CJSdcyMyVIF6f4hgoGRfvMnWWeah4=";
    };

    buildInputs = passthru.millDeps.cache.ivyDepsList;

    nativeBuildInputs = [
      mill
      mill.jre
      circt-install
      mlir-install
      jextract-21
      lit
      scala-cli
      add-determinism
      makeWrapper
    ];

    shellHook = ''
      ${mill-ivy-env-shell-hook}

      mill -i mill.bsp.BSP/install
      # other commands
    '';

    env.CIRCT_INSTALL_PATH = circt-install;
    env.MLIR_INSTALL_PATH = mlir-install;
    env.JEXTRACT_INSTALL_PATH = jextract-21;
    env.LIT_INSTALL_PATH = lit;
    env.JAVA_TOOL_OPTIONS = "--enable-preview";

    outputs = [ "out" ];

    buildPhase = ''
      mill -i '__.assembly'
    '';

    installPhase = ''
      mkdir -p $out/share/java

      add-determinism -j $NIX_BUILD_CORES out/zaozi/assembly.dest/out.jar

      mv out/zaozi/assembly.dest/out.jar $out/share/java/elaborator.jar
    '';
  };
in
self
