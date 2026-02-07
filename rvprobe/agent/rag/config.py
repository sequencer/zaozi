"""Configuration for RAG system."""

from pathlib import Path

# Paths
PROJECT_ROOT = Path(__file__).parent.parent.parent.parent
SCALA_SOURCE_PATH = PROJECT_ROOT / "rvprobe" / "src" / "constraints" / "RVConstraints.scala"
CHROMA_DB_PATH = Path(__file__).parent / "chroma_db"
MODEL_CACHE_PATH = Path(__file__).parent / "models"

# Model Configuration
EMBEDDING_MODEL = "paraphrase-multilingual-MiniLM-L12-v2"  # Supports Chinese + English
# EMBEDDING_MODEL = "all-MiniLM-L6-v2"  # Fallback: English-only, faster

# Retrieval Configuration
DEFAULT_TOP_K = 10
MAX_CONTEXT_TOKENS = 2000  # Token budget for retrieved docs
RERANK_ENABLED = True

# ChromaDB Configuration
COLLECTION_NAME = "rvprobe_constraints"
DISTANCE_METRIC = "cosine"  # or "l2", "ip"

# Categories
CATEGORIES = ["range", "has", "instruction", "isa_extension"]
