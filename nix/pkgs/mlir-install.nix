# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>

{ symlinkJoin, libllvm, mlir }:
symlinkJoin {
  name = "mlir-install";
  paths = [
    libllvm
    mlir
    mlir.dev
  ];

  inherit (mlir) meta;
}
