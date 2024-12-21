# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>
{
  description = "Chisel Nix";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable-small";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = inputs@{ self, nixpkgs, flake-utils }:
    let overlay = import ./nix/overlay.nix;
    in {
      # System-independent attr
      inherit inputs;
      overlays.default = overlay;
    } // flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          overlays = [ overlay ];
          inherit system;
        };
      in
      {
        formatter = pkgs.nixpkgs-fmt;
        legacyPackages = pkgs;
        devShells.default = pkgs.mkShell ({
          inputsFrom = [ pkgs.zaozi.zaozi-assembly ];
          nativeBuildInputs = [  ];
          env = {
            CIRCT_INSTALL_PATH = pkgs.circt-full;
            JEXTRACT_INSTALL_PATH = pkgs.jextract-21;
          };
        });
      });
}
