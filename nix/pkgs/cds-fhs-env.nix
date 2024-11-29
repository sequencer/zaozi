# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2024 Jiuyang Liu <liu@jiuyang.me>
{ getEnv'
, fetchFromGitHub
}:
let
  nixpkgsSrcs = fetchFromGitHub {
    owner = "NixOS";
    repo = "nixpkgs";
    rev = "c374d94f1536013ca8e92341b540eba4c22f9c62";
    hash = "sha256-Z/ELQhrSd7bMzTO8r7NZgi9g5emh+aRKoCdaAv5fiO0=";
  };

  # The cds we have only support x86-64_linux
  lockedPkgs = import nixpkgsSrcs { system = "x86_64-linux"; };

  jasperHome = getEnv' "JASPER_HOME";
  cdsLicenseFile = getEnv' "CDS_LIC_FILE";
in
lockedPkgs.buildFHSEnv {
  name = "cds-fhs-env";

  profile = ''
    [ ! -e "${jasperHome}"  ] && echo "env JASPER_HOME='${jasperHome}' points to unknown location" && exit 1
    [ ! -d "${jasperHome}"  ] && echo "env JASPER_HOME='${jasperHome}' not accessible" && exit 1

    export JASPER_HOME=${jasperHome}
    export CDS_LIC_FILE=${cdsLicenseFile}
    export PATH=$JASPER_HOME/bin:$PATH
    export _oldCdsEnvPath="$PATH"
    preHook() {
      PATH="$PATH:$_oldCdsEnvPath"
    }
    export -f preHook
  '';
  targetPkgs = (ps: with ps; [
    dejavu_fonts
    libGL
    util-linux
    libxcrypt-legacy
    coreutils-full
    ncurses5
    gmp5
    bzip2
    glib
    bc
    time
    elfutils
    ncurses5
    e2fsprogs
    cyrus_sasl
    expat
    sqlite
    nssmdns
    (libkrb5.overrideAttrs rec {
      version = "1.18.2";
      src = fetchurl {
        url = "https://kerberos.org/dist/krb5/${lib.versions.majorMinor version}/krb5-${version}.tar.gz";
        hash = "sha256-xuTJ7BqYFBw/XWbd8aE1VJBQyfq06aRiDumyIIWHOuA=";
      };
      sourceRoot = "krb5-${version}/src";
    })
    (gnugrep.overrideAttrs rec {
      version = "3.1";
      doCheck = false;
      src = fetchurl {
        url = "mirror://gnu/grep/grep-${version}.tar.xz";
        hash = "sha256-22JcerO7PudXs5JqXPqNnhw5ka0kcHqD3eil7yv3oH4=";
      };
    })
    keyutils
    graphite2
    libpulseaudio
    libxml2
    gcc
    gnumake
    xorg.libX11
    xorg.libXft
    xorg.libXScrnSaver
    xorg.libXext
    xorg.libxcb
    xorg.libXau
    xorg.libXrender
    xorg.libXcomposite
    xorg.libXi
    xorg.libSM
    xorg.libICE
    fontconfig
    freetype
    zlib
  ]);
}
