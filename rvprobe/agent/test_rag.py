#!/usr/bin/env python3
"""
End-to-end test for RAG-enhanced RVProbe Agent.
"""

import sys
from agent import build_agent_graph

def test_agent_with_rag():
    """Test agent with RAG retrieval."""

    # Build agent
    agent = build_agent_graph()

    # Test query
    user_input = "Generate 3 ADDI instructions where rd and rs1 are both in range 1 to 5"

    print("=" * 60)
    print("🧪 Testing RAG-Enhanced Agent")
    print("=" * 60)
    print(f"Input: {user_input}\n")

    # Run agent
    initial_state = {
        "user_input": user_input,
        "dsl_code": "",
        "error_log": "",
        "retry_count": 0,
        "is_success": False,
        "instructions": "",
        "retrieved_docs": ""
    }

    try:
        final_state = agent.invoke(initial_state)

        print("\n" + "=" * 60)
        print("📊 Test Results")
        print("=" * 60)

        if final_state['is_success']:
            print("✅ Test PASSED")
            print(f"\n📝 Generated Instructions:")
            print(final_state['instructions'])
            return 0
        else:
            print("❌ Test FAILED")
            print(f"\n❌ Error:")
            print(final_state['error_log'])
            return 1

    except Exception as e:
        print(f"\n❌ Test FAILED with exception: {e}")
        import traceback
        traceback.print_exc()
        return 1

if __name__ == "__main__":
    sys.exit(test_agent_with_rag())
