# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>
{
  description = "Chisel Nix";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable-small";
    nixpkgs4circt.url = "github:NixOS/nixpkgs/nixos-unstable-small";
    flake-utils.url = "github:numtide/flake-utils";
    chisel-nix.url = "github:chipsalliance/chisel-nix/new-mill-flow";
  };

  outputs = inputs@{ self, nixpkgs, nixpkgs4circt, flake-utils, chisel-nix }:
    let overlay = (import ./nix/overlay.nix) { extraNixpkgsSrc = nixpkgs4circt; };
    in {
      # System-independent attr
      inherit inputs;
      overlays.default = overlay;
    } // flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          overlays = [ overlay chisel-nix.overlays.mill-flows ];
          inherit system;
        };
      in
      with pkgs;
      {
        formatter = nixpkgs-fmt;
        legacyPackages = pkgs;
        devShells.default = mkShell {
          inputsFrom = [ zaozi.zaozi-assembly ];
          nativeBuildInputs = [ nixd ];
          env = {
            CIRCT_INSTALL_PATH = circt-install;
            MLIR_INSTALL_PATH = mlir-install;
            JEXTRACT_INSTALL_PATH = jextract-21;
            LIT_INSTALL_PATH = lit;
            SCALA_CLI_INSTALL_PATH = scala-cli;
            RISCV_OPCODES_INSTALL_PATH = riscv-opcodes;
            # pass to jextract
            # Jextract splits the header class into multiple classes, which are combined via extending
            # Due to https://github.com/scala/bug/issues/9272 we cannot access static fields in superclass headers, we work around this by not splitting the header
            # https://github.com/openjdk/jextract/blob/8730fcf05c229d035b0db52ee6bd82622e9d03e9/src/main/java/org/openjdk/jextract/impl/ToplevelBuilder.java#L54
            JAVA_TOOL_OPTIONS = "--enable-preview -Djextract.decls.per.header=65535";
          };
        };
      });
}
