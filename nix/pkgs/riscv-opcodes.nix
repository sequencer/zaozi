# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>

{ stdenv
, fetchFromGitHub
}:

stdenv.mkDerivation {
  name = "riscv-opcodes";
  src = fetchFromGitHub {
    owner = "riscv";
    repo = "riscv-opcodes";
    rev = "6a1be96c8238d603a50d956ff1f91defa264785b";
    hash = "sha256-0pYCpkZkrFVfZHxrxsKh12aiRKGU73TF9gkm2X7aqKs=";
  };

  buildPhase = "true";

  installPhase = ''
    runHook preInstall
    mkdir -p $out

    cp $src/rv* $out/
    cp -r $src/unratified $out/
    cp $src/*.csv $out/
    runHook postInstall
  '';
}
