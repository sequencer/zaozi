"""
AgentRunner - Method A: Full Agent with RAG + LLM + DSL + Mill + Z3 + Auto-retry

Integrates the existing agent.py to run as part of the benchmark.
"""

import sys
import os
import time
from pathlib import Path

# Add project paths
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..')))
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../..')))

from benchmark.runners.base_runner import BaseRunner
from benchmark.test_suite.schemas import (
    TestCase,
    RunResult,
    CorrectnessMetrics,
    EfficiencyMetrics,
    RobustnessMetrics,
    FailureMode
)
from benchmark.utils.timing import MultiTimer

# Import agent components
try:
    from agent import build_agent_graph, AgentState
    AGENT_AVAILABLE = True
except ImportError as e:
    print(f"⚠️ Warning: Could not import agent: {e}")
    AGENT_AVAILABLE = False


class AgentRunner(BaseRunner):
    """
    Runner for Method A: Full Agent approach.

    This runner wraps the existing agent.py workflow:
    1. RAG retrieval
    2. LLM code generation
    3. Mill compilation
    4. Z3 verification
    5. Auto-retry on failure

    Tracks timing and metrics for each stage.
    """

    def __init__(self, config):
        """
        Initialize AgentRunner.

        Args:
            config: BenchmarkConfig with settings
        """
        super().__init__(config)

        if not AGENT_AVAILABLE:
            raise RuntimeError("Agent module not available. Cannot create AgentRunner.")

        # Build the agent graph once
        self.graph = build_agent_graph()

    def run(self, test_case: TestCase) -> RunResult:
        """
        Run the full agent workflow for a test case.

        Args:
            test_case: The test case to execute

        Returns:
            RunResult with metrics and generated assembly
        """
        print(f"\n{'='*60}")
        print(f"[AgentRunner] Running test case: {test_case.id}")
        print(f"Description: {test_case.description}")
        print(f"{'='*60}\n")

        # Initialize result template
        result = self._create_result_template(test_case, method="agent")

        # Multi-timer for tracking different phases
        timer = MultiTimer()
        timer.start("total")

        try:
            # Initialize agent state
            initial_state = AgentState(
                user_input=test_case.description,
                dsl_code="",
                error_log="",
                retry_count=0,
                is_success=False,
                instructions="",
                retrieved_docs=""
            )

            # Run agent graph
            # Note: We can't easily track individual node times without modifying agent.py
            # For now, we track total time and estimate phases
            timer.start("agent_execution")
            final_state = self.graph.invoke(initial_state)
            timer.stop("agent_execution")

            # Extract results
            result.success = final_state.get("is_success", False)
            result.assembly = final_state.get("instructions", "")
            result.error_log = final_state.get("error_log", "")
            result.raw_output = final_state.get("instructions", "")

            # Store metadata
            result.metadata = {
                "retry_count": final_state.get("retry_count", 0),
                "dsl_code": final_state.get("dsl_code", "")[:500],  # First 500 chars
                "retrieved_docs_length": len(final_state.get("retrieved_docs", ""))
            }

            # Determine failure mode if not successful
            failure_mode = FailureMode.NONE
            if not result.success:
                error_log = result.error_log.lower()
                if "unsat" in error_log:
                    failure_mode = FailureMode.UNSAT
                elif "compilation error" in error_log or "error" in error_log:
                    failure_mode = FailureMode.COMPILATION_ERROR
                elif "timeout" in error_log:
                    failure_mode = FailureMode.TIMEOUT
                else:
                    failure_mode = FailureMode.LLM_ERROR

            # Build robustness metrics
            retry_count = final_state.get("retry_count", 0)
            result.robustness = RobustnessMetrics(
                is_success=result.success,
                failure_mode=failure_mode,
                timed_out=failure_mode == FailureMode.TIMEOUT,
                first_attempt_success=(result.success and retry_count <= 1)
            )

        except Exception as e:
            result.success = False
            result.error_log = f"AgentRunner exception: {str(e)}"
            result.robustness = RobustnessMetrics(
                is_success=False,
                failure_mode=FailureMode.LLM_ERROR,
                timed_out=False,
                first_attempt_success=False
            )
            print(f"❌ Exception in AgentRunner: {e}")
            import traceback
            traceback.print_exc()

        finally:
            # Stop total timer
            timer.stop("total")

        # Build efficiency metrics
        # Note: Without modifying agent.py, we can't get detailed breakdown
        # We estimate based on typical ratios:
        # - RAG/Retrieve: ~5-10% of total
        # - LLM Generate: ~40-50% of total
        # - Compilation: ~30-40% of total
        # - Verification: ~10-20% of total
        total_time = timer.get("total")

        result.efficiency = EfficiencyMetrics(
            total_time=total_time,
            llm_time=total_time * 0.45,  # Estimate
            compilation_time=total_time * 0.35,  # Estimate
            verification_time=total_time * 0.15,  # Estimate
            llm_call_count=result.metadata.get("retry_count", 1),  # At least 1 call per attempt
            total_prompt_tokens=0,  # Not available without LLM callback
            total_completion_tokens=0,  # Not available without LLM callback
            estimated_cost=0.0,  # Will be calculated later based on token count
            retry_count=result.metadata.get("retry_count", 0)
        )

        # Print summary
        print(f"\n{'='*60}")
        if result.success:
            print(f"✅ [AgentRunner] Success!")
            instruction_count = len(result.assembly.strip().split('\n')) if result.assembly else 0
            print(f"   Generated {instruction_count} instructions")
        else:
            print(f"❌ [AgentRunner] Failed!")
            print(f"   Failure mode: {result.robustness.failure_mode.value}")
        print(f"   Total time: {total_time:.2f}s")
        print(f"   Retries: {result.metadata.get('retry_count', 0)}")
        print(f"{'='*60}\n")

        return result


def test_agent_runner():
    """Quick test of AgentRunner."""
    from benchmark.test_suite.test_cases import get_case_by_id
    from benchmark.test_suite.schemas import BenchmarkConfig

    print("Testing AgentRunner...")

    config = BenchmarkConfig(
        llm_model="gpt-4o",
        llm_temperature=0.0,
        timeout_seconds=300
    )

    runner = AgentRunner(config)
    print(f"Runner created: {runner}")

    # Test with simple case
    test_case = get_case_by_id("TC-S01")
    print(f"\nRunning test case: {test_case.id}")
    print(f"Description: {test_case.description}")

    result = runner.run(test_case)

    print("\n" + "="*60)
    print("RESULT:")
    print("="*60)
    print(f"Success: {result.success}")
    print(f"Assembly lines: {len(result.assembly.split(chr(10))) if result.assembly else 0}")
    print(f"Total time: {result.efficiency.total_time:.2f}s")
    print(f"Retry count: {result.metadata.get('retry_count', 0)}")
    if not result.success:
        print(f"Error: {result.error_log[:200]}")


if __name__ == "__main__":
    test_agent_runner()
