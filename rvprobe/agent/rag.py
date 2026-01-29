"""
RAG retrieval engine for RVProbe Agent.
"""

from typing import List, Dict
from sentence_transformers import SentenceTransformer
import chromadb

from config import (
    CHROMA_DB_PATH,
    COLLECTION_NAME,
    EMBEDDING_MODEL,
    DEFAULT_TOP_K,
    MAX_CONTEXT_TOKENS,
    MODEL_CACHE_PATH
)


class RAGRetriever:
    """RAG retrieval system for constraint documentation."""

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

    def retrieve(self, user_query: str, top_k: int = DEFAULT_TOP_K) -> str:
        """
        Main retrieval method.

        Args:
            user_query: Natural language constraint description (supports Chinese/English)
            top_k: Number of results to return

        Returns:
            Formatted documentation string for LLM prompt
        """

        # Generate query embedding
        query_embedding = self.embedder.encode(user_query, convert_to_tensor=False)

        # Query ChromaDB
        results = self.collection.query(
            query_embeddings=[query_embedding.tolist()],
            n_results=top_k
        )

        # Format results
        formatted_docs = self._format_results(
            results['ids'][0],
            results['metadatas'][0],
            results['documents'][0]
        )

        return formatted_docs

    def _format_results(self, ids: List[str], metadatas: List[Dict], documents: List[str]) -> str:
        """Format retrieved documents for LLM context."""

        output = "# RVProbe Scala DSL API Reference\n\n"
        output += "## Retrieved Constraint Functions\n\n"

        for func_id, meta in zip(ids, metadatas):
            output += f"""### {func_id}
**Category**: {meta['category']}
**Description**: {meta['description']}

**Example**:
```scala
{meta['example_usage']}
```

"""

        # Add core patterns
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
    rdRange(1, 32) & rs1Range(1, 32)
  }
}
```

### Combining Constraints
Use `&` (AND), `|` (OR), `!` (NOT):
```scala
rdRange(1, 16) & rs1Range(1, 16) & imm12Range(0, 100)
```

### ISA Extension Selection
```scala
object test extends RVGenerator:
  val sets = isRV64GC()  // or isRV32I(), isRV64I(), etc.
  def constraints() =
    // your constraints here
```
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
