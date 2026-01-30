"""
Data schemas for benchmark framework.

Defines all data classes for test cases, results, and metrics.
"""

from dataclasses import dataclass, field, asdict
from typing import Dict, List, Optional, Any
from enum import Enum


class Difficulty(str, Enum):
    """Test case difficulty levels."""
    SIMPLE = "simple"
    MEDIUM = "medium"
    COMPLEX = "complex"


class FailureMode(str, Enum):
    """Types of failures that can occur."""
    NONE = ""
    UNSAT = "unsat"
    COMPILATION_ERROR = "compilation_error"
    TIMEOUT = "timeout"
    INVALID_ASSEMBLY = "invalid_assembly"
    LLM_ERROR = "llm_error"


@dataclass
class TestCase:
    """Definition of a test case."""

    id: str  # e.g., "TC-S01"
    difficulty: Difficulty
    description: str  # Natural language description of requirements

    # Expected constraints
    expected_count: int  # Expected number of instructions
    instruction_types: List[str]  # Allowed instruction mnemonics, e.g., ["addi", "addw"]
    register_constraints: Dict[str, Dict[str, int]]  # e.g., {"rd": {"min": 1, "max": 10}}
    immediate_constraints: Optional[Dict[str, int]] = None  # e.g., {"min": -100, "max": 100}

    # Metadata
    category: str = ""  # e.g., "arithmetic", "memory", "mixed"
    notes: str = ""

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for serialization."""
        return asdict(self)


@dataclass
class CorrectnessMetrics:
    """Correctness-related metrics."""

    is_valid_syntax: bool  # Whether assembly syntax is valid
    constraint_satisfaction_rate: float  # 0.0 to 1.0
    count_match: bool  # Whether instruction count matches expected
    type_correctness: float  # Proportion of correct instruction types (0.0-1.0)

    register_constraint_violations: int  # Number of register constraint violations
    immediate_constraint_violations: int  # Number of immediate constraint violations

    correctness_score: float  # Weighted overall score (0.0-1.0)

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary."""
        return asdict(self)


@dataclass
class EfficiencyMetrics:
    """Efficiency-related metrics."""

    total_time: float  # End-to-end time in seconds
    llm_time: float  # Time spent in LLM calls
    compilation_time: Optional[float] = None  # Mill compilation time (Method A only)
    verification_time: Optional[float] = None  # Z3 solving time (Method A only)

    llm_call_count: int = 0  # Number of LLM API calls
    total_prompt_tokens: int = 0
    total_completion_tokens: int = 0
    estimated_cost: float = 0.0  # In USD

    retry_count: int = 0  # Number of retries (Method A only)

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary."""
        return asdict(self)


@dataclass
class RobustnessMetrics:
    """Robustness-related metrics."""

    is_success: bool  # Overall success flag
    failure_mode: FailureMode  # Type of failure if not successful
    timed_out: bool  # Whether execution timed out

    first_attempt_success: bool  # Success on first attempt (no retries)

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary."""
        return asdict(self)


@dataclass
class RunResult:
    """Result of running a test case with a specific method."""

    test_id: str  # References TestCase.id
    method: str  # "agent" or "direct_llm" or "direct_llm_with_docs"

    # Output
    success: bool
    assembly: str  # Generated assembly instructions

    # Metrics
    correctness: Optional[CorrectnessMetrics] = None
    efficiency: Optional[EfficiencyMetrics] = None
    robustness: Optional[RobustnessMetrics] = None

    # Raw data for debugging
    raw_output: str = ""  # Full LLM or agent output
    error_log: str = ""  # Error messages if any
    metadata: Dict[str, Any] = field(default_factory=dict)  # Additional data

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for serialization."""
        result = {
            "test_id": self.test_id,
            "method": self.method,
            "success": self.success,
            "assembly": self.assembly,
            "raw_output": self.raw_output,
            "error_log": self.error_log,
            "metadata": self.metadata,
        }

        if self.correctness:
            result["correctness"] = self.correctness.to_dict()
        if self.efficiency:
            result["efficiency"] = self.efficiency.to_dict()
        if self.robustness:
            result["robustness"] = self.robustness.to_dict()

        return result

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'RunResult':
        """Create from dictionary."""
        correctness = None
        if "correctness" in data and data["correctness"]:
            correctness = CorrectnessMetrics(**data["correctness"])

        efficiency = None
        if "efficiency" in data and data["efficiency"]:
            efficiency = EfficiencyMetrics(**data["efficiency"])

        robustness = None
        if "robustness" in data and data["robustness"]:
            robustness = RobustnessMetrics(**data["robustness"])

        return cls(
            test_id=data["test_id"],
            method=data["method"],
            success=data["success"],
            assembly=data["assembly"],
            correctness=correctness,
            efficiency=efficiency,
            robustness=robustness,
            raw_output=data.get("raw_output", ""),
            error_log=data.get("error_log", ""),
            metadata=data.get("metadata", {}),
        )


@dataclass
class BenchmarkConfig:
    """Configuration for benchmark execution."""

    # LLM settings
    llm_model: str = "gpt-4o"
    llm_temperature: float = 0.0
    llm_max_tokens: int = 4000

    # Execution settings
    timeout_seconds: int = 300  # 5 minutes per test
    max_retries: int = 3  # For Method A

    # Cost calculation (per 1M tokens)
    prompt_token_cost: float = 0.0025  # $2.50 per 1M tokens
    completion_token_cost: float = 0.010  # $10.00 per 1M tokens

    # Output settings
    results_dir: str = "./benchmark_results"
    save_raw_outputs: bool = True

    # Parallel execution
    parallel_execution: bool = False
    max_workers: int = 4

    # Repetitions for statistical validity
    num_repetitions: int = 1  # Run each test N times

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary."""
        return asdict(self)

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'BenchmarkConfig':
        """Create from dictionary."""
        return cls(**data)
