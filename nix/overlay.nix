# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>
{ extraNixpkgsSrc }:

final: prev:

let
  extraNixpkgs = import extraNixpkgsSrc { inherit (final) system; };
in
{
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

  circt = extraNixpkgs.circt.overrideAttrs (prevAttrs: {
    patches = (prevAttrs.patches or [ ]) ++ [
      # [OM] Add missing CAPI omTypeIsAMapType
      (prev.fetchpatch {
        url = "https://github.com/llvm/circt/commit/7728eb3cd836958fe1a3f4b81da8a4d981228f71.patch";
        sha256 = "sha256-aVGnTVuZYlz8HuXVLfeYCtgC1YnVwcVpiQKn1bJFsaA=";
      })
      # [OM] Fix tuple_get operation in OMEvaluator
      (prev.fetchpatch {
        url = "https://github.com/llvm/circt/commit/62dd6304b046527b8472d6f446b28be975624b6c.patch";
        sha256 = "sha256-ranoZulCy+PDStJ13hWWE2I1CagTEVIsYCMnJlJq25A=";
      })
      # [OM] Fix finalization of nested ReferenceValue
      (prev.fetchpatch {
        url = "https://github.com/llvm/circt/commit/df2484d447eefe06b3c244f2786a93081c9032ef.patch";
        sha256 = "sha256-h03X8IMUlwBG884QGoeieWq07kmqCkoHFQp+IplxbB8=";
      })
    ];
  });

  circt-install = final.callPackage ./pkgs/circt-install.nix { };

  mlir-install = final.callPackage ./pkgs/mlir-install.nix { };

  riscv-opcodes = final.callPackage ./pkgs/riscv-opcodes.nix { };

  zaozi = final.callPackage ./zaozi { };
}
