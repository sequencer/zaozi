{ stdenv
, fetchFromGitHub
, cmake
, ninja
, asciidoctor
}:
stdenv.mkDerivation {
  name = "espresso";

  nativeBuildInputs = [
    cmake
    ninja
  ];
  buildInputs = [
    asciidoctor
  ];

  src = fetchFromGitHub {
    owner = "chipsalliance";
    repo = "espresso";
    rev = "0288253ca9459539d341bb1ada10406a74efc721";
    sha256 = "sha256-PZd5haLtqoKCcTIIiVAV0v0tHSPmpWkp6wcUgOGye98=";
  };
}
