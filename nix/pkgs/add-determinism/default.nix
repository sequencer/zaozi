# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>

{ lib
, rustPlatform
, fetchFromGitHub
, pkg-config
, zlib
, python3
, cargoLockFile ? ./Cargo.lock
, ...
}@args:

let
  marshalparser = args.marshalparser or python3.pkgs.callPackage ./marshalparser.nix { };
  pyEnv = python3.withPackages (ps: [ marshalparser ]);
in
rustPlatform.buildRustPackage {
  pname = "add-determinism";
  version = "unstable-2024-10-17";

  src = fetchFromGitHub {
    owner = "keszybz";
    repo = "add-determinism";
    rev = "d3748ff2ee13d61aa913d7c1160e9e2274742bad";
    hash = "sha256-IiIxUDYtq4Qcd9hTHsSqZEeETu5Vw3Gh6GxfArxBPG0=";
  };

  # this project has no Cargo.lock now
  cargoLock = {
    lockFile = cargoLockFile;
  };

  postPatch = ''
    ln -s ${cargoLockFile} Cargo.lock
  '';

  passthru = { inherit pyEnv marshalparser; };

  nativeBuildInputs = [
    pyEnv
    pkg-config
  ];

  propagatedBuildInputs = [ pyEnv ];

  buildInputs = [
    zlib
  ];

  meta = with lib; {
    description = "Build postprocessor to reset metadata fields for build reproducibility";
    homepage = "https://github.com/keszybz/add-determinism";
    license = licenses.gpl3Only;
    mainProgram = "add-determinism";
  };
}
