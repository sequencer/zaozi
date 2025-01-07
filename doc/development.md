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
- [MLIR](https://github.com/llvm/circt/) provided by `MLIR_INSTALL_PATH`,
  version of MLIR should match to CIRCT.
- [Lit](https://llvm.org/docs/CommandGuide/lit.html) provided by 
  `LIT_INSTALL_PATH` for running lit tests under zaozi.

The version of the dependencies are managed by nix, since CI only checks with
Nix, users should use version that provided by Nix.

## IDE Setup
You can use `nix develop` to enter the development environment in the Nix flow,
after you installed the dependencies and set the env. You can use
`mill mill.bsp.BSP/install` to config BSP and open with Intellij IDEA or metal.

## Swap CIRCT for development
Zaozi always follows the latest version of CIRCT. To use the specific version
of CIRCT for development, you override the circt version in nix script. You can
also compile CIRCT:
- software prerequisite: `cmake`, `clang`, `ninja`, `python3`, `ccache`
```shell
git clone git@github.com:llvm/circt $CIRCT_SOURCE
cmake -G Ninja \
  -B build \
  -DBUILD_SHARED_LIBS=ON \
  -DCMAKE_BUILD_TYPE=Debug \
  -DLLVM_ENABLE_PROJECTS=mlir \
  -DLLVM_ENABLE_ASSERTIONS=ON \
  -DLLVM_BUILD_EXAMPLES=OFF \
  -DLLVM_ENABLE_OCAMLDOC=OFF \
  -DLLVM_ENABLE_BINDINGS=OFF \
  -DLLVM_BUILD_TOOLS=ON \
  -DLLVM_OPTIMIZED_TABLEGEN=ON \
  -DLLVM_INCLUDE_TOOLS=ON \
  -DLLVM_USE_SPLIT_DWARF=ON \
  -DLLVM_BUILD_LLVM_DYLIB=ON \
  -DLLVM_LINK_LLVM_DYLIB=OFF \
  -DLLVM_CCACHE_BUILD=ON \
  -DLLVM_EXTERNAL_PROJECTS=circt \
  -DLLVM_EXTERNAL_CIRCT_SOURCE_DIR=$CIRCT_SOURCE
ninja -C build
```
configure the `CIRCT_INSTALL_PATH` to `build`, and run tests.
