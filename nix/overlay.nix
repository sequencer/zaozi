# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>
{ }:

final: prev:

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

  jextract-21 =
    (prev.jextract-21.override { llvmPackages = final.llvmPackages_20; }).overrideAttrs
      (old: {
        version = "unstable-2025-11-12";
        src = final.fetchFromGitHub {
          owner = "openjdk";
          repo = "jextract";
          rev = "0f87c6cdd5d63a7148deb38e16ed4de1306a4573";
          hash = "sha256-Bji7I6LNMs70drGo5+75OClCrxhOsoLV2V7Wdct6494=";
        };
      });

  # XXX: should handle in circt-nix?
  mlir = prev.llvmPackages_circt.mlir.override { buildSharedLibs = true; };
  libllvm = prev.llvmPackages_circt.libllvm.override { buildSharedLibs = true; };
  circt = prev.circt.override { buildSharedLibs = true; inherit (final) libllvm mlir; };

  circt-install = final.callPackage ./pkgs/circt-install.nix { };

  mlir-install = final.callPackage ./pkgs/mlir-install.nix { };

  riscv-opcodes = final.callPackage ./pkgs/riscv-opcodes.nix { };

  espresso = final.callPackage ./pkgs/espresso.nix { };

  zaozi = final.callPackage ./zaozi { };
}
