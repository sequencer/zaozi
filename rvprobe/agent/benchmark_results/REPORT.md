# RVProbe Agent Benchmark Report

**Generated**: 2026-02-07 18:03:57

**Configuration:**
- Model: Qwen/Qwen2.5-Coder-32B-Instruct
- Temperature: 0.0
- Timeout: 300s
- Total Results: 30

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [Method Comparison](#method-comparison)
3. [Results by Difficulty Level](#results-by-difficulty-level)
4. [Performance Analysis](#performance-analysis)
5. [Failure Analysis](#failure-analysis)
6. [Recommendations](#recommendations)
7. [Visualizations](#visualizations)

---

## Executive Summary

### Agent

- **Overall Success Rate**: 13/15 (86.7%)
- **Average Execution Time**: 10.265s
- **Total API Cost**: $0.0000
- **Average Correctness Score**: 0.867
- **Average Retry Count**: 1.13

### Direct Llm No Docs

- **Overall Success Rate**: 15/15 (100.0%)
- **Average Execution Time**: 17.195s
- **Total API Cost**: $0.0002
- **Average Correctness Score**: 0.949

## Method Comparison

| Metric | Agent | Direct Llm No Docs | Winner |
|--------|--------|--------|--------|
| Success Rate (%) | 86.7 | 100.0 | **Direct Llm No Docs** |
| Avg Time (s) | 10.265 | 17.195 | **Agent** |
| Total Cost ($) | $0.0000 | $0.0002 | **Agent** |
| Avg Correctness | 0.867 | 0.949 | **Direct Llm No Docs** |

## Results by Difficulty Level

### Simple Tests

| Method | Success Rate | Avg Time (s) | Avg Correctness |
|--------|--------------|--------------|-----------------|
| Agent | 100.0% (5/5) | 8.911 | 1.000 |
| Direct Llm No Docs | 100.0% (5/5) | 2.302 | 1.000 |

### Medium Tests

| Method | Success Rate | Avg Time (s) | Avg Correctness |
|--------|--------------|--------------|-----------------|
| Agent | 100.0% (5/5) | 7.760 | 1.000 |
| Direct Llm No Docs | 100.0% (5/5) | 12.820 | 1.000 |

### Complex Tests

| Method | Success Rate | Avg Time (s) | Avg Correctness |
|--------|--------------|--------------|-----------------|
| Agent | 60.0% (3/5) | 14.123 | 0.600 |
| Direct Llm No Docs | 100.0% (5/5) | 36.465 | 0.847 |

## Performance Analysis

### Agent

**Execution Time Statistics:**

- Mean: 10.265s
- Median (P50): 8.381s
- P95: 18.691s
- P99: 21.808s
- Range: [6.382s, 22.587s]
- Std Dev: 4.507s

**Correctness Score Statistics:**

- Mean: 0.867
- Median: 1.000
- Range: [0.000, 1.000]

### Direct Llm No Docs

**Execution Time Statistics:**

- Mean: 17.195s
- Median (P50): 9.513s
- P95: 57.712s
- P99: 57.983s
- Range: [1.579s, 58.050s]
- Std Dev: 18.423s

**Correctness Score Statistics:**

- Mean: 0.949
- Median: 1.000
- Range: [0.538, 1.000]

## Failure Analysis

### Agent

**Total Failures**: 2/15 (13.3%)

**Failure Modes:**

- Compilation Error: 1 (50.0%)
- Llm Error: 1 (50.0%)

**Failed Test Cases:**

- `TC-C04` (complex) - compilation_error
- `TC-C05` (complex) - llm_error

**Detailed Failure Cases:**

#### TC-C04 - Generate approximately 100 add-like instructions (ADDI, ADD, ADDW) with fuzzy count specification

- **Expected Count**: 100
- **Instruction Types**: addi, add, addw
- **Failure Mode**: compilation_error
- **Retry Count**: 3

**Generated DSL Code:**

```scala
(0 until 100).foreach { i =>
  val opcode = i % 3 match {
    case 0 => isAddi()
    case 1 => isAdd()
    case 2 => isAddw()
  }
  instruction(i, opcode) {
    rdRange(1, 32) & rs1Range(1, 32) & (if (opcode == isAddi()) imm12Range(-100, 100) else rs2Range(1, 32))
  }
}
```

**Compilation Error:**

```
[300] [error] -- [E172] Type Error: /home/clo91eaf/Project/zaozi/rvprobe/src/agent/Test.scala:19:28 
[300] [error] 19 |          case 0 => isAddi()
[300] [error]    |                            ^
[300] [error]    |No given instance of type me.jiuyang.rvprobe.constraints.Index was found for parameter x$4 of method isAddi in package me.jiuyang.rvprobe.constraints
[300] [error] -- [E172] Type Error: /home/clo91eaf/Project/zaozi/rvprobe/src/agent/Test.scala:20:27 
[300] [error] 20 |          case 1 => isAdd()
[300] [error]    |                           ^
[300] [error]    |No given instance of type me.jiuyang.rvprobe.constraints.Index was found for parameter x$4 of method isAdd in package me.jiuyang.rvprobe.constraints
[300] [error] -- [E172] Type Error: /home/clo91eaf/Project/zaozi/rvprobe/src/agent/Test.scala:21:28 
[300] [error] 21 |          case 2 => isAddw()
... (truncated)
```

---

#### TC-C05 - Generate 500 mixed instructions (all types) as a stress test for maximum volume

- **Expected Count**: 500
- **Instruction Types**: addi, add, addw, sub, subw...
- **Failure Mode**: llm_error
- **Retry Count**: 0
---

### Direct Llm No Docs

✓ No failures recorded

## Recommendations

### When to Use Each Method

**For Maximum Accuracy**: Use **Direct Llm No Docs**
- Success rate: 100.0%
- Average correctness: 0.949

**For Fastest Execution**: Use **Agent**
- Average time: 10.265s

**For Lowest Cost**: Use **Agent**
- Total cost: $0.0000

### General Recommendations

- Consider using faster method for simple cases and verified method for complex constraints
- Implement timeout mechanisms for production use
- Monitor API costs in production environments

## Visualizations

### Success Rate by Difficulty

![Success Rate by Difficulty](success_rate_by_difficulty.png)

### Execution Time Distribution

![Execution Time Distribution](time_distribution.png)

### API Cost Comparison

![API Cost Comparison](cost_comparison.png)

### Correctness Score Distribution

![Correctness Score Distribution](correctness_scores.png)

### Failure Mode Distribution

![Failure Mode Distribution](failure_modes.png)


---

*Report generated by RVProbe Benchmark Framework*
