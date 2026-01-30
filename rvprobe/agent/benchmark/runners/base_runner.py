"""
Abstract base class for test runners.

Defines the interface that all runners must implement.
"""

from abc import ABC, abstractmethod
from typing import Optional
import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../..')))

from benchmark.test_suite.schemas import TestCase, RunResult, BenchmarkConfig


class BaseRunner(ABC):
    """
    Abstract base class for instruction generation methods.

    All concrete runners (AgentRunner, DirectLLMRunner) must inherit from this
    and implement the run() method.
    """

    def __init__(self, config: BenchmarkConfig):
        """
        Initialize the runner with configuration.

        Args:
            config: Benchmark configuration containing LLM settings, timeouts, etc.
        """
        self.config = config

    @abstractmethod
    def run(self, test_case: TestCase) -> RunResult:
        """
        Execute the instruction generation for a given test case.

        Args:
            test_case: The test case to execute

        Returns:
            RunResult containing the generated assembly, metrics, and status

        Raises:
            TimeoutError: If execution exceeds config.timeout_seconds
            Exception: Other errors during execution
        """
        pass

    def _create_result_template(self, test_case: TestCase, method: str) -> RunResult:
        """
        Create a template RunResult with default values.

        Useful for initializing results before populating with actual data.

        Args:
            test_case: The test case being run
            method: The method identifier (e.g., "agent", "direct_llm")

        Returns:
            RunResult with test_id and method set, other fields at defaults
        """
        return RunResult(
            test_id=test_case.id,
            method=method,
            success=False,
            assembly="",
            raw_output="",
            error_log="",
            metadata={}
        )

    def validate_config(self) -> bool:
        """
        Validate that the runner configuration is correct.

        Returns:
            True if configuration is valid

        Raises:
            ValueError: If configuration is invalid
        """
        if self.config.timeout_seconds <= 0:
            raise ValueError("timeout_seconds must be positive")
        if self.config.llm_temperature < 0 or self.config.llm_temperature > 1:
            raise ValueError("llm_temperature must be in [0, 1]")
        if not self.config.llm_model:
            raise ValueError("llm_model must be specified")
        return True

    def __repr__(self) -> str:
        """String representation of the runner."""
        return f"{self.__class__.__name__}(model={self.config.llm_model})"
