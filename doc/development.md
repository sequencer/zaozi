# Development Documentation

The Zaozi project is a Scala project that links to CIRCT with the
[Project Panama](https://openjdk.org/projects/panama/).

## Development Flow
### Nix Flow

Zaozi by default use the nix flow to help you to get anything done for zaozi 
development in linux or darwin.

### Non-Nix Flow
For the development reason, e.g. swap to a debug version of CIRCT, or don't
want to use nix for development. You need to prepare such dependencies:
- [mill](https://mill-build.org) for build system in env.
- [JDK 21](https://openjdk.org/projects/jdk/21/) for setup Java environment, 
  zaozi only support the latest stable JDK version.
- [jextract](https://github.com/openjdk/jextract) provided by `JEXTRACT_INSTALL_PATH`
- [CIRCT](https://github.com/llvm/circt/) provided by `CIRCT_INSTALL_PATH`

The version of the dependencies are managed by nix, since CI only checks with
Nix, users should use version that provided by Nix.

## IDE Setup
You can use `nix develop` to enter the development environment in the Nix flow,
after you installed the dependencies and set the env. You can use
`mill mill.bsp.BSP/install` to config BSP and open with Intellij IDEA or metal.