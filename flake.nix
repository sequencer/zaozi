# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>
{
  description = "Zaozi: A Scala-based hardware design framework leveraging MLIR and CIRCT";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable-small";
    circt-src = {
      type = "github";
      owner = "llvm";
      repo = "circt";
      ref = "main";
      flake = false;
    };
    llvm-src = {
      type = "github";
      owner = "llvm";
      repo = "llvm-project";
      # from CIRCT submodule
      rev = "b7c1a6f8b447fba6fff47d309eb7ba1bc22e8c53";
      flake = false;
    };
    circt-nix = {
      url = "github:unlsycn/circt-nix";
      inputs = { nixpkgs.follows = "nixpkgs"; circt-src.follows = "circt-src"; llvm-submodule-src.follows = "llvm-src"; };
    };
    flake-utils.url = "github:numtide/flake-utils";
    mill-ivy-fetcher.url = "github:Avimitin/mill-ivy-fetcher";
  };

  outputs = inputs@{ self, nixpkgs, flake-utils, mill-ivy-fetcher, circt-nix, ... }:
    let overlay = (import ./nix/overlay.nix) { };
    in {
      # System-independent attr
      inherit inputs;
      overlays.default = overlay;
    } // flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          overlays = [ circt-nix.overlays.default overlay mill-ivy-fetcher.overlays.default ];
          inherit system;
        };
      in
      {
        formatter = pkgs.nixpkgs-fmt;
        legacyPackages = pkgs;
        packages = {
          default = pkgs.zaozi.zaozi-assembly;
          zaozi-assembly = pkgs.zaozi.zaozi-assembly;
        };
        devShells.default = pkgs.mkShell {
          inputsFrom = [ pkgs.zaozi.zaozi-assembly ];
          nativeBuildInputs = with pkgs; [ nixd ];
          env = with pkgs;
            {
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
