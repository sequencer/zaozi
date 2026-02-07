"""
RAG retrieval engine for RVProbe Agent.
"""

from typing import List, Dict
from sentence_transformers import SentenceTransformer
import chromadb

from .config import (
    CHROMA_DB_PATH,
    COLLECTION_NAME,
    EMBEDDING_MODEL,
    DEFAULT_TOP_K,
    MAX_CONTEXT_TOKENS,
    MODEL_CACHE_PATH
)


class RAGRetriever:
    """RAG retrieval system for constraint documentation."""

    # Known instruction name mappings: common names -> actual DSL API names
    INSTRUCTION_ALIASES = {
        "slli": ["isSlliRV64I", "isSlliRV32I", "isSlliw"],
        "srli": ["isSrliRV64I", "isSrliRV32I", "isSrliw"],
        "srai": ["isSraiRV64I", "isSraiRV32I", "isSraiw"],
    }

    # When these instructions appear, also retrieve these range functions
    INSTRUCTION_REQUIRED_RANGES = {
        "slli": ["shamtdRange", "shamtwRange"],
        "srli": ["shamtdRange", "shamtwRange"],
        "srai": ["shamtdRange", "shamtwRange"],
        "slliw": ["shamtwRange"],
        "srliw": ["shamtwRange"],
        "sraiw": ["shamtwRange"],
        "addi": ["imm12Range"],
        "andi": ["imm12Range"],
        "ori":  ["imm12Range"],
        "xori": ["imm12Range"],
        "slti": ["imm12Range"],
        "lw":   ["imm12Range"],
        "ld":   ["imm12Range"],
        "sw":   ["imm12Range"],
        "sd":   ["imm12Range"],
        "lui":  ["imm20Range"],
        "auipc":["imm20Range"],
        "beq":  ["bimm12hiRange", "bimm12loRange"],
        "bne":  ["bimm12hiRange", "bimm12loRange"],
        "blt":  ["bimm12hiRange", "bimm12loRange"],
        "bge":  ["bimm12hiRange", "bimm12loRange"],
    }

    # Pattern keyword -> pattern document IDs to fetch
    PATTERN_KEYWORDS = {
        "raw": ["pattern_raw_dependency", "pattern_raw_chain_simple"],
        "read-after-write": ["pattern_raw_dependency", "pattern_raw_chain_simple"],
        "data dependency": ["pattern_raw_dependency", "pattern_raw_chain_simple"],
        "data hazard": ["pattern_raw_dependency", "pattern_raw_chain_simple"],
        "dependency chain": ["pattern_raw_dependency", "pattern_raw_chain_simple"],
        "mixed": ["pattern_mixed_types", "pattern_match_dispatch"],
        "interleave": ["pattern_match_dispatch"],
        "round-robin": ["pattern_match_dispatch"],
        "partition": ["pattern_register_partition"],
        "register partition": ["pattern_register_partition"],
        "pin register": ["pattern_register_pinning"],
        "register pinning": ["pattern_register_pinning"],
        "exact register": ["pattern_register_pinning"],
        "shift": ["pattern_shift_instructions"],
        "slli": ["pattern_shift_instructions"],
        "srli": ["pattern_shift_instructions"],
        "srai": ["pattern_shift_instructions"],
        "stress": ["pattern_stress_test"],
        "large": ["pattern_stress_test"],
        "anti-pattern": ["pattern_anti_patterns"],
        "wrong": ["pattern_anti_patterns"],
        "mistake": ["pattern_anti_patterns"],
    }

    def __init__(self):
        """Initialize ChromaDB client and embedding model."""
        self.client = chromadb.PersistentClient(path=str(CHROMA_DB_PATH))
        self.collection = self.client.get_collection(COLLECTION_NAME)

        # Load embedding model
        MODEL_CACHE_PATH.mkdir(exist_ok=True)
        self.embedder = SentenceTransformer(
            EMBEDDING_MODEL,
            cache_folder=str(MODEL_CACHE_PATH)
        )

        # Build ID lookup for direct retrieval
        all_docs = self.collection.get(include=['metadatas'])
        self._id_set = set(all_docs['ids'])
        self._id_to_meta = {id: meta for id, meta in zip(all_docs['ids'], all_docs['metadatas'])}

    def _extract_instruction_names(self, query: str) -> List[str]:
        """Extract instruction mnemonics from query text (e.g., 'SLLI', 'addi')."""
        import re
        # Match common RISC-V instruction patterns (case-insensitive)
        tokens = re.findall(r'\b([A-Za-z]{2,10}[wWdD]?)\b', query)
        known_instructions = set()

        # All known R-type instructions (no special range needed but need direct lookup)
        r_type_instructions = {
            "add", "addw", "sub", "subw",
            "and", "or", "xor",
            "sll", "srl", "sra", "sllw", "srlw", "sraw",
            "slt", "sltu",
            "mul", "mulh", "mulhsu", "mulhu", "mulw",
            "div", "divu", "divw", "divuw",
            "rem", "remu", "remw", "remuw",
        }
        all_known = set(self.INSTRUCTION_REQUIRED_RANGES.keys()) | set(self.INSTRUCTION_ALIASES.keys()) | r_type_instructions

        for token in tokens:
            lower = token.lower()
            if lower in all_known:
                known_instructions.add(lower)
        return list(known_instructions)

    def _get_docs_by_ids(self, ids: List[str]) -> tuple:
        """Directly fetch documents by their IDs."""
        # Deduplicate while preserving order
        seen = set()
        unique_ids = []
        for id in ids:
            if id in self._id_set and id not in seen:
                unique_ids.append(id)
                seen.add(id)
        if not unique_ids:
            return [], [], []
        results = self.collection.get(ids=unique_ids, include=['metadatas', 'documents'])
        return results['ids'], results['metadatas'], results['documents']

    def retrieve(self, user_query: str, top_k: int = DEFAULT_TOP_K) -> str:
        """
        Enhanced retrieval with pattern matching, multi-query decomposition and direct ID lookup.

        Strategy:
        0. Match pattern keywords -> fetch pattern recipe documents
        1. Extract instruction names from query -> direct ID lookup for exact matches
        2. Look up required range functions for each instruction
        3. Semantic search for remaining context
        4. Deduplicate and format
        """
        all_ids = []
        all_metas = []
        all_docs = []
        seen_ids = set()

        # --- Phase 0: Pattern document lookup ---
        pattern_ids = self._match_pattern_keywords(user_query)
        # Always include anti-patterns and basic loop for complex queries
        if pattern_ids:
            pattern_ids.append("pattern_anti_patterns")
            pattern_ids.append("pattern_basic_loop")
        if pattern_ids:
            p_ids, p_metas, p_docs = self._get_docs_by_ids(pattern_ids)
            for id, meta, doc in zip(p_ids, p_metas, p_docs):
                if id not in seen_ids:
                    all_ids.append(id)
                    all_metas.append(meta)
                    all_docs.append(doc)
                    seen_ids.add(id)

        # --- Phase 1: Direct lookup for mentioned instructions ---
        instruction_names = self._extract_instruction_names(user_query)
        direct_lookup_ids = []

        for inst_name in instruction_names:
            # Check for aliases (e.g., slli -> isSlliRV64I, isSlliRV32I)
            if inst_name in self.INSTRUCTION_ALIASES:
                direct_lookup_ids.extend(self.INSTRUCTION_ALIASES[inst_name])
            else:
                # Try standard naming: slli -> isSlli, addi -> isAddi
                camel = inst_name[0].upper() + inst_name[1:]
                candidate = f"is{camel}"
                if candidate in self._id_set:
                    direct_lookup_ids.append(candidate)

            # Also fetch required range functions
            if inst_name in self.INSTRUCTION_REQUIRED_RANGES:
                direct_lookup_ids.extend(self.INSTRUCTION_REQUIRED_RANGES[inst_name])

        if direct_lookup_ids:
            ids, metas, docs = self._get_docs_by_ids(direct_lookup_ids)
            for id, meta, doc in zip(ids, metas, docs):
                if id not in seen_ids:
                    all_ids.append(id)
                    all_metas.append(meta)
                    all_docs.append(doc)
                    seen_ids.add(id)

        # --- Phase 2: Semantic search for broader context ---
        remaining_k = max(top_k - len(all_ids), 5)
        query_embedding = self.embedder.encode(user_query, convert_to_tensor=False)
        results = self.collection.query(
            query_embeddings=[query_embedding.tolist()],
            n_results=remaining_k
        )

        for id, meta, doc in zip(results['ids'][0], results['metadatas'][0], results['documents'][0]):
            if id not in seen_ids:
                all_ids.append(id)
                all_metas.append(meta)
                all_docs.append(doc)
                seen_ids.add(id)

        # --- Phase 3: Multi-query for mixed instruction types ---
        # If query mentions multiple instruction types, do a sub-query per type
        if len(instruction_names) > 1:
            for inst_name in instruction_names[:5]:  # Cap at 5 sub-queries
                sub_query = f"{inst_name} instruction constraint"
                sub_embedding = self.embedder.encode(sub_query, convert_to_tensor=False)
                sub_results = self.collection.query(
                    query_embeddings=[sub_embedding.tolist()],
                    n_results=3
                )
                for id, meta, doc in zip(sub_results['ids'][0], sub_results['metadatas'][0], sub_results['documents'][0]):
                    if id not in seen_ids:
                        all_ids.append(id)
                        all_metas.append(meta)
                        all_docs.append(doc)
                        seen_ids.add(id)

        # Format results
        formatted_docs = self._format_results(all_ids, all_metas, all_docs)
        return formatted_docs

    def _match_pattern_keywords(self, query: str) -> List[str]:
        """Match pattern keywords in the query and return relevant pattern doc IDs."""
        query_lower = query.lower()
        matched_ids = []
        for keyword, pattern_ids in self.PATTERN_KEYWORDS.items():
            if keyword in query_lower:
                matched_ids.extend(pattern_ids)
        # Deduplicate
        seen = set()
        result = []
        for id in matched_ids:
            if id not in seen:
                result.append(id)
                seen.add(id)
        return result

    def _format_results(self, ids: List[str], metadatas: List[Dict], documents: List[str]) -> str:
        """Format retrieved documents for LLM context, grouped by category."""

        # Group by category for better organization
        by_category = {}
        for func_id, meta, doc in zip(ids, metadatas, documents):
            cat = meta['category']
            if cat not in by_category:
                by_category[cat] = []
            by_category[cat].append((func_id, meta, doc))

        output = "# RVProbe Scala DSL API Reference\n\n"

        # Show PATTERN documents first (most important for understanding HOW to write code)
        if 'pattern' in by_category:
            output += "## Constraint Patterns & Recipes\n\n"
            output += "These patterns show HOW to compose constraints for common scenarios.\n\n"
            for func_id, meta, doc in by_category['pattern']:
                output += f"### {meta['description']}\n\n"
                output += f"```scala\n{meta['example_usage']}\n```\n\n"
            output += "---\n\n"

        output += "## Retrieved Constraint Functions\n\n"

        # Show instruction functions first, then range, then others
        category_order = ['instruction', 'range', 'has', 'isa_extension']
        for cat in category_order:
            if cat not in by_category:
                continue
            output += f"### {cat.replace('_', ' ').title()} Functions\n\n"
            for func_id, meta, _doc in by_category[cat]:
                output += f"#### {func_id}\n"
                output += f"**Description**: {meta['description']}\n\n"
                output += f"**Example**:\n```scala\n{meta['example_usage']}\n```\n\n"

        # Add core patterns and IMPORTANT warnings
        output += """
## Core Patterns

### Instruction Definition
```scala
instruction(index, opcodeConstraint) {
  argumentConstraints
}
```

### Loop Pattern
```scala
(0 until N).foreach { i =>
  instruction(i, isAddi()) {
    rdRange(1, 32) & rs1Range(1, 32) & imm12Range(-100, 100)
  }
}
```

### Combining Constraints
Use `&` (AND) to combine:
```scala
rdRange(1, 16) & rs1Range(1, 16) & imm12Range(0, 100)
```

## IMPORTANT WARNINGS
- There is NO `isSlli()`, `isSrli()`, or `isSrai()` function. Use `isSlliRV64I()` or `isSlliRV32I()`.
- There is NO `shamtRange()` or `immRange()` function. Use `shamtwRange()`, `shamtdRange()`, or `imm12Range()`.
- Do NOT use Scala standard library (Array.fill, var, mutable state) inside instruction() blocks.
- Only use constraint functions (rdRange, rs1Range, imm12Range, etc.) combined with `&` inside instruction() blocks.
"""

        return output


# Singleton instance for easy import
_retriever_instance = None


def get_retriever() -> RAGRetriever:
    """Get or create singleton RAG retriever instance."""
    global _retriever_instance
    if _retriever_instance is None:
        _retriever_instance = RAGRetriever()
    return _retriever_instance
