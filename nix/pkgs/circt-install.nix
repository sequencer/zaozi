# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>

{ symlinkJoin, circt }:
symlinkJoin {
  name = "circt-install";
  paths = [
    circt
    circt.lib
    circt.dev
  ];

  inherit (circt) meta;
}
