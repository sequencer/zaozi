"""
Constraint pattern documentation for RAG indexing.

These are NOT API functions, but usage patterns that teach the LLM
how to combine API functions to achieve common constraint goals.
"""

from typing import List, Dict


# Each pattern is a document that will be indexed in ChromaDB
CONSTRAINT_PATTERNS: List[Dict[str, str]] = [
    # ==================== Basic Patterns ====================
    {
        "id": "pattern_basic_loop",
        "category": "pattern",
        "subcategory": "basic",
        "description": "Basic loop pattern: generate N instructions of the same type with constraints. Use (0 until N).foreach to iterate.",
        "example_usage": """(0 until 20).foreach { i =>
  instruction(i, isAddi()) {
    rdRange(1, 32) & rs1Range(1, 32) & imm12Range(-100, 100)
  }
}""",
        "content": "Basic loop pattern for generating multiple identical instructions. Use (0 until N).foreach { i => instruction(i, opcode()) { constraints } }. The index i must be unique per instruction. Combine argument constraints with & operator.",
    },
    {
        "id": "pattern_mixed_types",
        "category": "pattern",
        "subcategory": "basic",
        "description": "Mixed instruction types: generate different instruction types using separate loop ranges. Each range covers a contiguous block of indices.",
        "example_usage": """// 10 ADDI + 10 SLLI + 10 XOR = 30 total
(0 until 10).foreach { i =>
  instruction(i, isAddi()) {
    rdRange(1, 32) & rs1Range(1, 32) & imm12Range(-100, 100)
  }
}
(10 until 20).foreach { i =>
  instruction(i, isSlliRV64I()) {
    rdRange(1, 32) & rs1Range(1, 32) & shamtdRange(0, 31)
  }
}
(20 until 30).foreach { i =>
  instruction(i, isXor()) {
    rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
  }
}""",
        "content": "To mix different instruction types, use separate (start until end).foreach loops with non-overlapping index ranges. Each instruction type gets its own loop. Total count = sum of all ranges. IMPORTANT: instruction indices must not overlap between loops.",
    },
    {
        "id": "pattern_match_dispatch",
        "category": "pattern",
        "subcategory": "basic",
        "description": "Match-based dispatch: use modulo and pattern matching to interleave different instruction types within a single loop.",
        "example_usage": """(0 until 30).foreach { i =>
  (i % 3) match {
    case 0 => instruction(i, isAddi()) {
      rdRange(1, 32) & rs1Range(1, 32) & imm12Range(-100, 100)
    }
    case 1 => instruction(i, isSlliRV64I()) {
      rdRange(1, 32) & rs1Range(1, 32) & shamtdRange(0, 31)
    }
    case 2 => instruction(i, isXor()) {
      rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
    }
  }
}""",
        "content": "To interleave instruction types in a round-robin fashion, use (i % N) match with N being the number of types. This distributes types evenly. IMPORTANT: use isSlliRV64I() not isSlli(), use shamtdRange() not shamtRange().",
    },

    # ==================== RAW Dependency Pattern ====================
    {
        "id": "pattern_raw_dependency",
        "category": "pattern",
        "subcategory": "dependency",
        "description": "RAW (Read-After-Write) data dependency chain: each instruction reads from the register that the previous instruction wrote to. Achieves this by constraining rd and rs1 to specific register values using rdRange(r, r+1) & rs1Range(r, r+1) patterns.",
        "example_usage": """// RAW chain: instruction i reads from register that instruction i-1 wrote to
// Use register rotation: rd=1,rs1=1 -> rd=2,rs1=1 -> rd=3,rs1=2 -> ...
(0 until 50).foreach { i =>
  val regDst = (i % 30) + 1   // rd cycles through 1-30
  val regSrc = if (i == 0) 1 else ((i - 1) % 30) + 1  // rs1 = previous rd
  instruction(i, isAddi()) {
    rdRange(regDst, regDst + 1) & rs1Range(regSrc, regSrc + 1) & imm12Range(-10, 10)
  }
}""",
        "content": "RAW (Read-After-Write) dependency: each instruction's source register (rs1) should equal the previous instruction's destination register (rd). IMPORTANT: Do NOT use Array.fill(), var, or mutable state inside instruction blocks. Instead, compute rd and rs1 from the loop index i using arithmetic expressions. Use rdRange(r, r+1) to pin a register to exact value r. The key insight is that register values can be derived from the loop index i.",
    },
    {
        "id": "pattern_raw_chain_simple",
        "category": "pattern",
        "subcategory": "dependency",
        "description": "Simple RAW dependency chain using two alternating registers. Instruction i writes to register A while reading from register B, then instruction i+1 does the reverse.",
        "example_usage": """// Simple 2-register RAW chain: alternating between x1 and x2
(0 until 50).foreach { i =>
  if (i % 2 == 0) {
    instruction(i, isAddi()) {
      rdRange(1, 2) & rs1Range(2, 3) & imm12Range(-10, 10)
    }
  } else {
    instruction(i, isAddi()) {
      rdRange(2, 3) & rs1Range(1, 2) & imm12Range(-10, 10)
    }
  }
}""",
        "content": "Simplest RAW dependency: alternate between two registers. Even instructions: rd=x1, rs1=x2. Odd instructions: rd=x2, rs1=x1. This creates a strict read-after-write chain. Do NOT use mutable variables or Array.fill() - only use loop index arithmetic and if/else.",
    },

    # ==================== Register Constraint Patterns ====================
    {
        "id": "pattern_register_partition",
        "category": "pattern",
        "subcategory": "register",
        "description": "Register partitioning: use non-overlapping ranges for rd and rs1 to ensure destination and source registers are from different sets.",
        "example_usage": """(0 until 100).foreach { i =>
  instruction(i, isAddi()) {
    rdRange(1, 6) & rs1Range(10, 21) & imm12Range(-2048, 2047)
  }
}""",
        "content": "Register partitioning means rd and rs1 use different register ranges. For example, rd in x1-x5 and rs1 in x10-x20. This ensures no overlap between destination and source registers. Just use different min/max values in rdRange and rs1Range.",
    },
    {
        "id": "pattern_register_pinning",
        "category": "pattern",
        "subcategory": "register",
        "description": "Pin a register to a specific value by using range of size 1: rdRange(n, n+1) constrains rd to exactly register xN.",
        "example_usage": """// Pin rd to x5 for all instructions
(0 until 10).foreach { i =>
  instruction(i, isAddi()) {
    rdRange(5, 6) & rs1Range(1, 32) & imm12Range(0, 100)
  }
}""",
        "content": "To constrain a register to an exact value N, use rdRange(N, N+1). The range is half-open [min, max), so rdRange(5, 6) means rd = x5. This works for all range functions: rs1Range(10, 11) means rs1 = x10.",
    },

    # ==================== Shift Instruction Patterns ====================
    {
        "id": "pattern_shift_instructions",
        "category": "pattern",
        "subcategory": "shift",
        "description": "Shift instructions (SLLI/SRLI/SRAI): MUST use isSlliRV64I()/isSrliRV64I()/isSraiRV64I() for 64-bit, and shamtdRange() for shift amount. There is NO isSlli() or shamtRange() function.",
        "example_usage": """// CORRECT: shift instructions for RV64I
(0 until 10).foreach { i =>
  instruction(i, isSlliRV64I()) {
    rdRange(1, 32) & rs1Range(1, 32) & shamtdRange(0, 32)
  }
}
(10 until 20).foreach { i =>
  instruction(i, isSrliRV64I()) {
    rdRange(1, 32) & rs1Range(1, 32) & shamtdRange(0, 32)
  }
}
// WRONG: isSlli() does NOT exist! Use isSlliRV64I() instead.
// WRONG: shamtRange() does NOT exist! Use shamtdRange() or shamtwRange() instead.""",
        "content": "CRITICAL: For shift instructions, the function names include the ISA suffix. Use isSlliRV64I() (not isSlli()), isSrliRV64I() (not isSrli()), isSraiRV64I() (not isSrai()). For shift amount constraints, use shamtdRange(min, max) for 64-bit shifts or shamtwRange(min, max) for 32-bit shifts. There is NO shamtRange() function.",
    },

    # ==================== Large Scale / Stress Test Patterns ====================
    {
        "id": "pattern_stress_test",
        "category": "pattern",
        "subcategory": "scale",
        "description": "Large-scale stress test: generate hundreds of mixed instructions by dividing the total count into equal segments per instruction type.",
        "example_usage": """// 100 instructions: 5 types × 20 each
val typeCount = 5
val perType = 20
// Type 1: ADDI (indices 0-19)
(0 until perType).foreach { i =>
  instruction(i, isAddi()) {
    rdRange(1, 32) & rs1Range(1, 32) & imm12Range(-2048, 2047)
  }
}
// Type 2: ADD (indices 20-39)
(perType until 2 * perType).foreach { i =>
  instruction(i, isAdd()) {
    rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
  }
}
// Type 3: SLLI (indices 40-59)
(2 * perType until 3 * perType).foreach { i =>
  instruction(i, isSlliRV64I()) {
    rdRange(1, 32) & rs1Range(1, 32) & shamtdRange(0, 31)
  }
}
// ... continue for remaining types""",
        "content": "For stress tests with many instruction types, divide total count evenly among types. Use separate loops with non-overlapping index ranges. Common instruction types: isAddi() (I-type), isAdd()/isSub()/isXor()/isAnd()/isOr() (R-type), isSlliRV64I()/isSrliRV64I() (shift), isBeq()/isBne() (branch), isLw()/isSw() (memory).",
    },

    # ==================== Anti-Patterns (What NOT to do) ====================
    {
        "id": "pattern_anti_patterns",
        "category": "pattern",
        "subcategory": "warning",
        "description": "Common mistakes and anti-patterns in DSL code generation. Do NOT use mutable state, Array.fill, or incorrect API names.",
        "example_usage": """// ❌ WRONG: Array.fill is Scala standard library, NOT part of the DSL
// val rd = Array.fill(50)(0)  // COMPILE ERROR!

// ❌ WRONG: isSlli() does not exist
// instruction(i, isSlli()) { ... }  // COMPILE ERROR!

// ❌ WRONG: shamtRange() does not exist
// shamtRange(0, 31)  // COMPILE ERROR!

// ❌ WRONG: immRange() does not exist
// immRange(-100, 100)  // COMPILE ERROR!

// ✅ CORRECT alternatives:
// isSlliRV64I() instead of isSlli()
// shamtdRange(0, 31) instead of shamtRange()
// imm12Range(-100, 100) instead of immRange()""",
        "content": "ANTI-PATTERNS to avoid: 1) Do NOT use Array.fill(), var, val with mutable state inside instruction blocks. 2) Do NOT use isSlli()/isSrli()/isSrai() - use isSlliRV64I()/isSrliRV64I()/isSraiRV64I(). 3) Do NOT use shamtRange() - use shamtdRange() or shamtwRange(). 4) Do NOT use immRange() - use imm12Range() or imm20Range(). The constraint DSL only accepts pure constraint expressions combined with &.",
    },
]


def get_all_patterns() -> list:
    """Return all constraint patterns for indexing."""
    return CONSTRAINT_PATTERNS
