# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>
{ extraNixpkgsSrc }:

final: prev:

let
  extraNixpkgs = import extraNixpkgsSrc { inherit (final) system; };
in
{
  espresso = final.callPackage ./pkgs/espresso.nix { };

  mill =
    let jre = final.jdk21;
    in (prev.mill.override { inherit jre; }).overrideAttrs
      (_: rec {
        version = "0.11.12";
        src = final.fetchurl {
          url = "https://github.com/com-lihaoyi/mill/releases/download/${version}/${version}-assembly";
          hash = "sha256-k4/oMHvtq5YXY8hRlX4gWN16ClfjXEAn6mRIoEBHNJo=";
        };
        passthru = { inherit jre; };
      });

  fetchMillDeps = final.callPackage ./pkgs/mill-builder.nix { };

  inherit (extraNixpkgs) circt;
  circt-install = final.callPackage ./pkgs/circt-install.nix { };

  mlir-install = final.callPackage ./pkgs/mlir-install.nix { };

  # faster strip-undetereminism
  add-determinism = final.callPackage ./pkgs/add-determinism { };

  projectDependencies = final.callPackage ./pkgs/project-dependencies.nix { };

  zaozi = final.callPackage ./zaozi { };
}
