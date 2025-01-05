# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>

{ symlinkJoin, circt }:
symlinkJoin {
  name = "circt-full";
  paths = [
    circt
    circt.lib
    circt.dev

    circt.llvm
    circt.llvm.lib
    circt.llvm.dev
  ];

  inherit (circt) meta;
}
