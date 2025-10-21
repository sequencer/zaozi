# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>
{ extraNixpkgsSrc, sn-bindgen }:

final: prev:

let
  extraNixpkgs = import extraNixpkgsSrc { inherit (final) system; };
in
{
  mill = let jre = final.jdk21; in
    (prev.mill.override { inherit jre; }).overrideAttrs rec {
      version = "1.0.0";
      src = final.fetchurl {
        url = "https://repo1.maven.org/maven2/com/lihaoyi/mill-dist/${version}/mill-dist-${version}.exe";
        hash = "sha256-pgkwME2xs4ezfWS1HGFS2uPIqqvECTOAILWmCqci2Aw=";
      };
      propagatedBuildInputs = with prev; [ which ];
      doInstallCheck = false;
      passthru = { inherit jre; };
    };

  circt = extraNixpkgs.circt;

  circt-install = final.callPackage ./pkgs/circt-install.nix { };

  mlir-install = final.callPackage ./pkgs/mlir-install.nix { };

  riscv-opcodes = final.callPackage ./pkgs/riscv-opcodes.nix { };

  espresso = final.callPackage ./pkgs/espresso.nix { };

  zaozi = final.callPackage ./zaozi { };
}
