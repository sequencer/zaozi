# Rationale

This document describes why things in this repository are done the way they are as well as a discussion of alternatives. This is intended to be a historical document so that prior discussions are not forgotten.

## 

1. No more global builder anymore: Builder as [contextual](https://docs.scala-lang.org/scala3/reference/contextual/).
1. DSL only for module level, separate linking at CIRCT, lazy elaborate each module, defines as this to avoid call `architecture` at `new`.
```scala3
trait Module:
  // construct IO
  def interface: Interface
  // construct RTL
  def architecture: Unit
```
1. FIR Dialect Type in Scala(match to MLIR)

- Chisel Type in Scala(source compatible to chisel3, but well defined)
- Chisel Operation as typeclass
- native panama instantiation


## Thoughts
The core of Zaozi should be minimalist, excluding hardware implementations such as Queue and Arbiter, which should be provided by a separate standard library.
Zaozi's extensibility should be maximized, allowing users to integrate their preferred Dialects in CIRCT. Utilizing a C-API for lowering to CIRCT, it should serve as a universal frontend for diverse hardware architectures.


