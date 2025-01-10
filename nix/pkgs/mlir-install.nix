# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>

{ symlinkJoin, circt }:
symlinkJoin {
  name = "mlir-install";
  paths = [
    circt.llvm.lib
    circt.llvm.dev
  ];

  inherit (circt) meta;
}
