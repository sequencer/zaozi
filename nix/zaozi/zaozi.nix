# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>

{ lib
, stdenv
, fetchMillDeps
, makeWrapper
, jdk21
, mill
, circt-install
, mlir-install
, jextract-21
, lit
, scala-cli
, add-determinism
, projectDependencies
}:

let
  self = stdenv.mkDerivation rec {
    name = "zaozi";

    src = with lib.fileset;
      toSource {
        root = ./../..;
        fileset = unions [
          ./../../build.sc
          ./../../circtlib
          ./../../mlirlib
          ./../../zaozi
        ];
      };

    passthru.millDeps = fetchMillDeps {
      inherit name;
      src = with lib.fileset;
        toSource {
          root = ./../..;
          fileset = unions [ ./../../build.sc ];
        };
      millDepsHash =
        if stdenv.isDarwin then
          "sha256-5wHqKYd4Gn/FKhKLHrqeGmfa8OSQO+l/cuE4BMHiKpM="
        else
          "sha256-1oZ/MFsvA+Og+BjCYSWW51FodF6zZJisLJHzOsFDL7Y=";
      nativeBuildInputs = [ projectDependencies.setupHook ];
    };

    passthru.editable = self.overrideAttrs (_: {
      shellHook = ''
        setupSubmodulesEditable
        mill mill.bsp.BSP/install 0
      '';
    });

    shellHook = ''
      setupSubmodules
    '';

    nativeBuildInputs = [
      mill
      circt-install
      mlir-install
      jextract-21
      lit
      scala-cli
      add-determinism
      makeWrapper
      passthru.millDeps.setupHook
      projectDependencies.setupHook
    ];

    env.CIRCT_INSTALL_PATH = circt-install;
    env.MLIR_INSTALL_PATH = mlir-install;
    env.JEXTRACT_INSTALL_PATH = jextract-21;
    env.LIT_INSTALL_PATH = lit;

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
