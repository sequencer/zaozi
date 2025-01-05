# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>

{ lib
, rustPlatform
, fetchFromGitHub
, pkg-config
, zlib
, python3
, stdenv
, cargoLockFile ? ./Cargo.lock
, ...
}@args:

let
  marshalparser = args.marshalparser or python3.pkgs.callPackage ./marshalparser.nix { };
  pyEnv = python3.withPackages (ps: [ marshalparser ]);
in
rustPlatform.buildRustPackage {
  pname = "add-determinism";
  version = "unstable-2024-11-12";

  src = fetchFromGitHub {
    owner = "keszybz";
    repo = "add-determinism";
    rev = "aadcc2fc4648ce8c485fdd9c861eb11adb40c344";
    hash = "sha256-AanKDeFLBeLV5oHWiuPWNJirxDqQwKdZ9Szo5A7fVU8=";
  };

  # this project has no Cargo.lock now
  cargoLock = {
    lockFile = cargoLockFile;
  };

  patches = [
    ./fix-darwin-build.patch
  ];

  postPatch = ''
    ln -s ${./Cargo.lock} Cargo.lock
  '';

  doCheck = ! stdenv.isDarwin;  # it seems to be running forever

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
