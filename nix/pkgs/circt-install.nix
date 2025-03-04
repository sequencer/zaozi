# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>

{ symlinkJoin, circt, fetchpatch }:

let
  patchedCirct = circt.overrideAttrs (oldAttrs: rec {
    patches = (oldAttrs.patches or []) ++ [
      # [ExportSMTLIB] Implement C API
      (fetchpatch {
        url = "https://github.com/llvm/circt/commit/257426e53b8b1fc59c9923c09fe1a0aa5282f797.patch";
        sha256 = "sha256-AhTb61YOHUo47Kjzt+N4iE7d8OtnrWPbWYSlp3qvbuo=";
      })
      # [SMT][CAPI] Add more SMT C API
      (fetchpatch {
        url = "https://github.com/llvm/circt/commit/17fb5b522fd612c794d1be122612b442580d3c17.patch";
        sha256 = "sha256-VHFCZzMbo3+1eEC3Xn4HmRyQy5fPHJDeTP+EUoaXmB4=";
      })
    ];
  });
in
symlinkJoin {
  name = "circt-install";
  paths = [
    patchedCirct
    patchedCirct.lib
    patchedCirct.dev
  ];

  inherit (patchedCirct) meta;
}
