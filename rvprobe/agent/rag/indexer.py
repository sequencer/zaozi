#!/usr/bin/env python3
"""
Index management for RAG system.
Creates and updates ChromaDB vector database.
"""

import chromadb
from chromadb.config import Settings
from sentence_transformers import SentenceTransformer
from typing import List
import torch

from .extract_docs import main as extract_functions, ConstraintFunction
from .constraint_patterns import get_all_patterns
from .config import (
    CHROMA_DB_PATH,
    COLLECTION_NAME,
    EMBEDDING_MODEL,
    MODEL_CACHE_PATH,
    DISTANCE_METRIC
)


class IndexManager:
    """Manages ChromaDB index for constraint functions."""

    def __init__(self):
        """Initialize ChromaDB and embedding model."""

        # Create ChromaDB client
        CHROMA_DB_PATH.mkdir(exist_ok=True)
        self.client = chromadb.PersistentClient(
            path=str(CHROMA_DB_PATH),
            settings=Settings(anonymized_telemetry=False)
        )

        # Load embedding model
        print(f"📦 Loading embedding model: {EMBEDDING_MODEL}")
        MODEL_CACHE_PATH.mkdir(exist_ok=True)
        self.embedder = SentenceTransformer(
            EMBEDDING_MODEL,
            cache_folder=str(MODEL_CACHE_PATH)
        )

        # Use CPU for embeddings (faster for small batches)
        if torch.cuda.is_available():
            print("⚡ GPU available, using CUDA")
        else:
            print("💻 Using CPU for embeddings")

    def create_index(self, functions: List[ConstraintFunction], force_recreate: bool = False):
        """Create or update ChromaDB index with constraint functions."""

        # Check if collection exists
        try:
            collection = self.client.get_collection(COLLECTION_NAME)
            if force_recreate:
                print(f"🗑️  Deleting existing collection: {COLLECTION_NAME}")
                self.client.delete_collection(COLLECTION_NAME)
                collection = None
            else:
                print(f"✅ Collection already exists: {COLLECTION_NAME}")
                return collection
        except:
            collection = None

        # Create collection
        if collection is None:
            print(f"🆕 Creating collection: {COLLECTION_NAME}")
            collection = self.client.create_collection(
                name=COLLECTION_NAME,
                metadata={"description": "RVProbe constraint functions"},
                embedding_function=None  # We'll provide embeddings manually
            )

        # Generate embeddings and add to collection
        print(f"🔢 Generating embeddings for {len(functions)} functions...")

        # Prepare data
        ids = []
        documents = []
        embeddings = []
        metadatas = []

        for func in functions:
            ids.append(func.function_name)
            documents.append(func.to_content())

            # Generate embedding
            embedding = self.embedder.encode(func.to_content(), convert_to_tensor=False)
            embeddings.append(embedding.tolist())

            # Prepare metadata
            metadata = {
                "category": func.category,
                "subcategory": func.subcategory or "",
                "return_type": func.return_type,
                "description": func.description,
                "example_usage": func.example_usage,
                "signature": func.signature,
                "source_line": func.source_line,
                "related_functions": ",".join(func.related_functions),
            }
            metadatas.append(metadata)

        # Batch add to collection
        BATCH_SIZE = 100
        for i in range(0, len(ids), BATCH_SIZE):
            batch_end = min(i + BATCH_SIZE, len(ids))
            print(f"   Adding batch {i//BATCH_SIZE + 1}/{(len(ids)-1)//BATCH_SIZE + 1}...")

            collection.add(
                ids=ids[i:batch_end],
                embeddings=embeddings[i:batch_end],
                documents=documents[i:batch_end],
                metadatas=metadatas[i:batch_end]
            )

        print(f"✅ Index created successfully with {len(ids)} documents")

        return collection

    def add_patterns(self, collection):
        """Add constraint pattern documents to an existing collection."""
        patterns = get_all_patterns()
        if not patterns:
            print("⚠️  No constraint patterns found.")
            return

        print(f"📝 Adding {len(patterns)} constraint pattern documents...")

        ids = []
        documents = []
        embeddings = []
        metadatas = []

        for pat in patterns:
            doc_id = pat["id"]
            # Build a rich text for embedding that includes description, content, and example
            content = f"{pat['description']}\n\n{pat['content']}\n\nExample:\n{pat['example_usage']}"

            ids.append(doc_id)
            documents.append(content)

            embedding = self.embedder.encode(content, convert_to_tensor=False)
            embeddings.append(embedding.tolist())

            metadatas.append({
                "category": pat["category"],          # "pattern"
                "subcategory": pat.get("subcategory", ""),
                "return_type": "",
                "description": pat["description"],
                "example_usage": pat["example_usage"],
                "signature": "",
                "source_line": 0,
                "related_functions": "",
            })

        collection.add(
            ids=ids,
            embeddings=embeddings,
            documents=documents,
            metadatas=metadatas
        )

        print(f"✅ Added {len(ids)} pattern documents")

    def query_test(self, query: str, n_results: int = 5):
        """Test query against the index."""

        collection = self.client.get_collection(COLLECTION_NAME)

        # Generate query embedding
        query_embedding = self.embedder.encode(query, convert_to_tensor=False)

        # Query collection
        results = collection.query(
            query_embeddings=[query_embedding.tolist()],
            n_results=n_results
        )

        print(f"\n🔍 Query: '{query}'")
        print(f"📊 Top {n_results} results:")

        for i, (doc_id, metadata, distance) in enumerate(zip(
            results['ids'][0],
            results['metadatas'][0],
            results['distances'][0]
        ), 1):
            print(f"\n{i}. {doc_id} (distance: {distance:.4f})")
            print(f"   Category: {metadata['category']}")
            print(f"   Description: {metadata['description'][:100]}...")

    def get_stats(self):
        """Get statistics about the index."""

        collection = self.client.get_collection(COLLECTION_NAME)

        # Get all metadata
        all_items = collection.get()

        categories = {}
        for meta in all_items['metadatas']:
            cat = meta['category']
            categories[cat] = categories.get(cat, 0) + 1

        print("\n📊 Index Statistics:")
        print(f"   Total documents: {len(all_items['ids'])}")
        print(f"   Categories:")
        for cat, count in categories.items():
            print(f"      - {cat}: {count}")


def main():
    """Main indexing pipeline."""

    print("🚀 Starting indexing pipeline...")

    # Step 1: Extract functions from Scala source
    print("\n📖 Step 1: Extracting constraint functions from RVConstraints.scala")
    functions = extract_functions()

    # Step 2: Create ChromaDB index
    print("\n💾 Step 2: Creating ChromaDB index")
    manager = IndexManager()
    collection = manager.create_index(functions, force_recreate=True)

    # Step 3: Add constraint patterns to the same collection
    print("\n📝 Step 3: Adding constraint pattern documents")
    manager.add_patterns(collection)

    # Step 4: Get statistics
    manager.get_stats()

    # Step 5: Run test queries
    print("\n🧪 Step 5: Running test queries")
    test_queries = [
        "Generate ADDI instructions with register constraints",
        "SLLI instruction for RV64I",
        "Constrain destination register to range 1-16",
        "Load word instruction with immediate offset",
        "RAW data dependency chain",
        "How to mix different instruction types",
        "生成ADDI指令",  # Chinese test
    ]

    for query in test_queries:
        manager.query_test(query, n_results=5)

    print("\n✅ Indexing complete!")


if __name__ == "__main__":
    main()
