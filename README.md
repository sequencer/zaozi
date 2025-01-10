# Zaozi

Zaozi is an experimental project aimed at rewriting Chisel in pure Scala 3.
It will not replace Chisel, but provide a minimized solution to create an plugable eDSL in Scala 3.
The goal of this project is providing an eDSL frontend framework for hardware designs. 

## Project Structure

- **mlirlib**:
A Java module that maintains all MLIR C-API definitions.
It can be a generic layer for any MLIR infrastructure in Scala 3.

- **circtlib**:
A Java module that maintains all CIRCT C-API definitions, currently mainly for Firrtl.
Developers adding new dialects to Zaozi should expose them in CIRCT and include them here.

- **zaozi**:
The core DSL implementation, encompassing the type system and build entries.
It focuses on module-level construction, allowing modules to implement specific interfaces without extending from a base class.

## Design Philosophy

Zaozi emphasizes a modular and minimalistic approach, delegating build processes to MLIR via C-API.

This strategy reduces JVM memory usage by avoiding local AST storage and eliminates serialization overhead by directly binding MLIR values to Scala values via the MLIR C-API.

Additionally, Zaozi separates the eDSL API declaration with Scala 3 `given` pattern, supporting swap APIs implementation through `given` a type class.

## Licensing

The project is licensed under the Apache License 2.0.

© Jiuyang Liu <liu@jiuyang.me>. All Rights Reserved.
