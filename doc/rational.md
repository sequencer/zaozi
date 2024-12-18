# Rationale

This document describes why things in this repository are done the way they are
as well as a discussion of alternatives.
This is intended to be a historical document so that prior discussions are not
forgotten.

## Chisel is 凿子 (Zaozi), 凿子 (Zaozi) is Chisel

Zaozi is an experimental project that rewrites Chisel in Scala 3 with no
guarantee of compatibility. Its purpose is to eliminate the historical burdens
of Chisel while leveraging its valuable ideas from years of development. Zaozi
is not intended to replace Chisel but may eventually merge back into it as a
new package once it matures.

## Builder

The Zaozi builder leverages the [contextual of Scala](https://docs.scala-lang.org/scala3/reference/contextual/).

### Key Differences from Chisel

- Module Construction:
Unlike Chisel, which constructs the entire circuit at once, Zaozi focuses on
module-level construction. Modules do not extend from the `Module` class.
Instead, they implement specific interfaces (previously known as Bundles).

- Module Instantiation:
Modules are instantiated using a simple API that takes a bundle and a module
name. The details of the instantiated module are private and hidden within the
implementation. It helps large projects cut lines among different teams.

- Namespace Management:
Namespace management and linking are handled outside the Zaozi DSL. Users can
elaborate or instantiate modules with any names, and conflicts (e.g., namespace
clashes or linking errors) are detected during compiling by CIRCT.

### Design Philosophy

Zaozi simplifies the boundary between the build system and compiler. While
Chisel aims to handle everything for end-users, Zaozi acts as a minimalistic
tool, delegating build recipes to external systems. This approach:

- Cuts the line between RTL design and verification by limiting interface
construction.

- Reduces JVM memory usage by avoiding local AST storage, instead binding
`MLIRValue` to Scala values via MLIR C-API.

- Eliminates serialization and deserialization overhead, as Zaozi does not
generate strings for FIRRTL nor requires parsing them by firtool.


## Type System

The Zaozi type system is split into two levels:

### MLIR Type binding

Defined in `circtlib/src/FirrtlType.scala`, MLIR type bindings provide a
straightforward connection between Scala 3 and MLIR. Each MLIRType maps
one-to-one to its corresponding MLIR type via the C-API. This design allows
Zaozi to extend support for new MLIR dialects and maintain these extensions in
a separate package visible only to language designers.


### Zaozi DSL Types

Unlike Chisel, which stores references at runtime, Zaozi separates DSL
construction types from runtime types. DSL types, such as `UInt`, `SInt`, 
`Bits`, `Bool`, `Clock`, `Reset`, `Bundle`, and `Vec`, implement specific type
classes rather than inheriting from a common base. This:

- Supports user-defined types and operators through explicit imports.

- Simplifies the addition of new types by defining their type lowering and
implementing required type classes.

- The Zaozi Type only maintains the data at compiler time. For the rest of
things, they are user-input at DSL-runtime or queried from CIRCT via C-API.
This eliminates the misalignment between the DSL frontend and backend and 
reduces the maintenance burden and dirty hacks.

### Zaozi Aggregate Types
Aggregate is a useful feature for DSLs, Chisel provides `Bundle` and `Vec`, so
does Zaozi, the detail implementation is different, but shares the same design
principle.
#### Bundle
The `Bundle` type implementation in Scala is tricky, which almost goes into the
dependent type aspect, the simplicity of DSL language shouldn't require user to
understand such complex type system.
Chisel has a reflection-based `Bundle` that storing in the runtime, it provides
a simple design pattern to users. But it causes tons of issue to store and copy
the type at runtime.
Zaozi uses Scala dynamic to access internal types. Ideally, allowing user 
implementing their own `Bundle`-like types is most attractive. However, Jiuyang
tried two different approaches, and both of them are complained by compiler.
The X-problem is we need to dynamic access the bundle field from referent type.
`val a: [B <: Bundle, R <: Ref[B]: R`, and `a.someField` returns `Ref[T]`,
where `T` is the type of `someFiled` which should be inferred at compile time.
I tried two different approaches but failed: 
- typeclass way
```scala 3
trait [B <: SubAccess, R <: Ref[B]]: DynamicSubAccess[R] extends Dynamic:
  extension (ref: B)
    def selectDynamic(field: String): Any
```
It should be the simplest way to allow user implement their own `SubAccess` for
their own `Bundle`, however, Scala 3 forbid [this](https://github.com/scala/scala3/issues/22158).

- outer macro call inner macro to get type, see:
```scala 3
  // For each Bundle type, they need to implement a macro to get Type based on the field names.
  trait SubAccess:
    inline def getTypeWithString(fieldName: String): Any = ${ bundleGetTypeWithString('this, 'fieldName) }
    def bundleGetTypeWithString(bundle: Expr[Bundle], fieldName: Expr[String])(using Quotes): Expr[Any]
  // For the Ref type, it implements a macro to access type 
  trait Referable[T <: Data]:
    transparent inline def selectDynamic[R <: Data](name: String): Any = ${ dynamicSubaccess('this, 'name) }
    def dynamicSubaccess[T <: Data: Type](ref: Expr[Referable[T]], fieldName: Expr[String])(using Quotes): Expr[Any] =
      ???
      // call macro ref.tpe.getTypeWithString(fieldName)
      val callMacroExpr = '{
        ${ ref }.tpe.asInstanceOf[SubAccess].getTypeWithString(${ Expr(name) })
      }
      ???
```
And user can implement their own `SubAccess`, this seems attractive that user
can implement their own `SubAccess`, however the compiler is not happy with 
this:
```
Deferred inline method getTypeWithString in trait SubAccess cannot be invoked [19:9]
```
In the end, we fall back to provide the internal `Bundle`, and user cannot
implement their own `Bundle`-like type based on extending trait or implement
type class.

### Reference Type

Types for components like registers, instances, and wires are not managed
directly in the host language or MLIR. Instead, Zaozi uses a type system
expressed as `[T <: Data, R <: Ref[T]]: R`, where R can represent Register,
Wire, Instance, Node, or other referenceable components. This approach provides
clear semantics to end-users.

### Project Structural

Zaozi’s core is modular and well-structured:

- `circtpanamabinding`: A Java module maintaining all C-API definitions.
Developers adding new dialects to Zaozi should expose them in CIRCT and include
them here.

- `circtlib`: A Scala module defining MLIR type bindings in Zaozi, ensuring a
strict one-to-one mapping and API for type conversion.

- `zaozi`: The core DSL implementation, including the type system and build
entries. Hardware implementations are not included here, and the type system
will align with the Language Reference Manual (LRM) for compatibility.

- `stdlib`: A collection of hardware projects using Zaozi. It includes hardware
construction blocks (e.g., queues, arbiters, FP units) and advanced DSL-level
features like `BitSet`, `BitPat`, and decoder infrastructure.
