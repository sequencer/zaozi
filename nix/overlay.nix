# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>
{ extraNixpkgsSrc }:

final: prev:

let
  extraNixpkgs = import extraNixpkgsSrc { inherit (final) system; };
in
{
  espresso = final.callPackage ./pkgs/espresso.nix { };

  mill = let jre = final.jdk21; in
    (prev.mill.override { inherit jre; }).overrideAttrs rec {
      # Fixed the buggy sorting issue in target resolve
      version = "0.12.8-1-46e216";
      src = final.fetchurl {
        url = "https://repo1.maven.org/maven2/com/lihaoyi/mill-dist/${version}/mill-dist-${version}-assembly.jar";
        hash = "sha256-XNtl9NBQPlkYu/odrR/Z7hk3F01B6Rk4+r/8tMWzMm8=";
      };
      passthru = { inherit jre; };
    };

  fetchMillDeps = final.callPackage ./pkgs/mill-builder.nix { };

  inherit (extraNixpkgs) circt;
  circt-install = final.callPackage ./pkgs/circt-install.nix { };

  mlir-install = final.callPackage ./pkgs/mlir-install.nix { };

  # faster strip-undetereminism
  add-determinism = final.callPackage ./pkgs/add-determinism { };

  projectDependencies = final.callPackage ./pkgs/project-dependencies.nix { };

  riscv-opcodes = final.callPackage ./pkgs/riscv-opcodes.nix { };

  zaozi = final.callPackage ./zaozi { };
}
