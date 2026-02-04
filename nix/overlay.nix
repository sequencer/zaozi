# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>
final: prev:

{
  # XXX: should handle in circt-nix?
  mlir = prev.llvmPackages_circt.mlir.override { buildSharedLibs = true; };
  libllvm = prev.llvmPackages_circt.libllvm.override { buildSharedLibs = true; };
  circt = prev.circt.override {
    buildSharedLibs = true;
    inherit (final) libllvm mlir;
  };

  circt-install = final.callPackage ./pkgs/circt-install.nix { };

  mlir-install = final.callPackage ./pkgs/mlir-install.nix { };

  zaozi = final.callPackage ./zaozi { };
}
