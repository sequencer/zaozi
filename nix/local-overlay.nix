# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>
final: prev:

{
  mill = prev.millVersions.mill_1_1_2;

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

  riscv-opcodes = final.callPackage ./pkgs/riscv-opcodes.nix { };

  espresso = final.callPackage ./pkgs/espresso.nix { };
}
