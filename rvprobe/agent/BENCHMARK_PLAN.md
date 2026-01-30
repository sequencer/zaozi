# RVProbe-Agent Benchmark Framework Implementation Plan

## 项目目标

创建一个科学、公平、可复现的benchmark系统，对比两种RISC-V指令生成方法：

- **方法A (Full Agent)**: RAG检索 + LLM生成Scala DSL + Mill编译 + Z3验证 + 自动重试
- **方法B (Direct LLM)**: 纯LLM直接生成汇编指令，无验证流程

## 系统架构

```
测试用例 → 执行器 → 评估器 → 指标收集 → 可视化 → 报告
    ↓         ↓         ↓          ↓          ↓        ↓
  15个用例  AgentRunner  解析汇编  正确性/效率  图表   Markdown
           DirectLLMRunner 验证约束  鲁棒性      CSV
```

### 核心组件

1. **测试套件** - 15个测试用例（简单5 + 中等5 + 复杂5）
2. **执行器** - AgentRunner（方法A）、DirectLLMRunner（方法B）
3. **评估器** - 解析汇编、验证约束、计算指标
4. **可视化** - 成功率、时间分布、成本对比图表
5. **报告生成** - Markdown格式的详细对比报告

## 文件结构

```
rvprobe/agent/benchmark/
├── __init__.py
├── benchmark.py              # 主入口
├── config.yaml               # 配置文件
│
├── test_suite/
│   ├── __init__.py
│   ├── test_cases.py         # 15个测试用例定义
│   └── schemas.py            # TestCase数据类
│
├── runners/
│   ├── __init__.py
│   ├── base_runner.py        # 抽象基类
│   ├── agent_runner.py       # 方法A：完整agent
│   └── direct_llm_runner.py  # 方法B：纯LLM
│
├── evaluators/
│   ├── __init__.py
│   ├── assembly_parser.py    # 解析RISC-V汇编
│   ├── constraint_checker.py # 验证约束满足
│   └── metrics.py            # 指标计算
│
├── visualization/
│   ├── __init__.py
│   ├── visualizer.py         # 生成图表
│   └── report_generator.py   # Markdown报告
│
└── utils/
    ├── __init__.py
    └── timing.py             # 计时工具
```

## 测试用例设计

### 简单类别（5个）

**TC-S01**: 10条ADDI，rd范围1-10
**TC-S02**: 20条ADDI，rd和rs1范围1-31，imm范围-100到100
**TC-S03**: 15条SLLI，shift amount范围0-10
**TC-S04**: 10条LW，rs1范围2-10
**TC-S05**: 8条BEQ，rs1和rs2范围1-15

### 中等类别（5个）

**TC-M01**: 50条混合（25 ADDI + 25 ADDW）
**TC-M02**: 100条ADDI，rd范围1-5，rs1范围10-20（寄存器分区）
**TC-M03**: 60条混合算术（ADDI/SLTI/ANDI），imm范围0-255
**TC-M04**: 40条内存操作（20 LW + 20 SW）
**TC-M05**: 75条混合（SLLI/SRLI/XOR）

### 复杂类别（5个）

**TC-C01**: 200条ADDI，严格约束（rd和rs1范围1-8，imm范围-50到50）
**TC-C02**: 50条ADDI，要求连续RAW依赖（跨索引约束）
**TC-C03**: 150条高度混合（50算术+40逻辑+30移位+30分支）
**TC-C04**: ~100条（模糊数量），add-like指令，模糊约束表达
**TC-C05**: 500条压力测试（混合类型，最大数量）

## 评估指标

### 正确性指标

- `is_valid_syntax`: 汇编语法是否正确
- `constraint_satisfaction_rate`: 约束满足率（0.0-1.0）
- `count_match`: 生成数量是否匹配
- `type_correctness`: 指令类型正确率
- `register_constraint_violations`: 寄存器约束违反次数
- `immediate_constraint_violations`: 立即数约束违反次数
- `correctness_score`: 综合正确性得分（加权平均）

### 效率指标

- `total_time`: 端到端时间（秒）
- `llm_time`: LLM调用时间
- `compilation_time`: Mill编译时间（仅方法A）
- `verification_time`: Z3求解时间（仅方法A）
- `llm_call_count`: LLM调用次数
- `total_prompt_tokens`: 总prompt token数
- `total_completion_tokens`: 总completion token数
- `estimated_cost`: 估算API成本（美元）
- `retry_count`: 重试次数（仅方法A）

### 鲁棒性指标

- `is_success`: 总体成功标志
- `first_attempt_success_rate`: 首次尝试成功率
- `final_success_rate`: 最终成功率（含重试）
- `failure_mode`: 失败类型（unsat/compilation_error/timeout/invalid_assembly）
- `timed_out`: 是否超时

## 实现计划

### Phase 1: 基础框架（第1周）

**关键文件**：
1. `test_suite/schemas.py` - 定义TestCase、RunResult、CorrectnessMetrics等数据类
2. `test_suite/test_cases.py` - 定义15个测试用例
3. `runners/base_runner.py` - 抽象基类，定义run()接口
4. `config.yaml` - 配置文件模板

**验证**：
- 能够加载测试用例
- 数据类正确序列化/反序列化

### Phase 2: 执行器实现（第2周）

**关键文件**：
1. `runners/agent_runner.py` - 集成现有agent.py
   - 包装agent.invoke()调用
   - 跟踪各阶段时间（RAG/Generate/Execute/Decide）
   - 提取token使用量
   - 处理重试逻辑

2. `runners/direct_llm_runner.py` - 实现纯LLM生成
   - 构建有效的prompt
   - 调用LLM API
   - 解析LLM响应提取汇编指令
   - 支持两个变体：无文档/有文档

**验证**：
- 两个runner能独立运行简单测试用例
- 正确返回RunResult对象

### Phase 3: 评估器实现（第3周）

**关键文件**：
1. `evaluators/assembly_parser.py` - 解析RISC-V汇编
   - 正则表达式匹配指令格式：`\d+:\s+\w+\s+.*`
   - 提取指令助记符、寄存器、立即数
   - 返回结构化指令列表

2. `evaluators/constraint_checker.py` - 验证约束
   - 检查指令数量
   - 检查指令类型分布
   - 验证寄存器范围
   - 验证立即数范围
   - 计算constraint_satisfaction_rate

3. `evaluators/metrics.py` - 计算所有指标
   - 组合CorrectnessMetrics、EfficiencyMetrics、RobustnessMetrics
   - 成本估算（基于token用量和价格）

**验证**：
- 能正确解析有效汇编指令
- 能检测约束违反
- 指标计算合理

### Phase 4: 编排与执行（第4周）

**关键文件**：
1. `benchmark.py` - 主编排器
   - 加载测试用例
   - 为每个测试用例运行两个方法
   - 调用评估器
   - 收集结果
   - 保存到CSV/JSON

**功能**：
- 顺序执行（默认）
- 并行执行（可选，用于独立测试）
- 进度显示
- 错误处理

**验证**：
- 完整执行所有15个测试用例
- 生成results_summary.csv和results_detailed.json

### Phase 5: 可视化与报告（第5周）

**关键文件**：
1. `visualization/visualizer.py` - 生成图表
   - 成功率对比（按难度分组）
   - 时间分布直方图
   - 复杂度扩展曲线
   - 成本对比柱状图
   - 失败模式饼图

2. `visualization/report_generator.py` - Markdown报告
   - 执行摘要
   - 方法对比表格
   - 按难度细分结果
   - 性能分析（P50/P95/P99）
   - 失败分析
   - 建议

**验证**：
- 生成所有图表（PNG格式，300dpi）
- 生成完整的REPORT.md
- 报告可读性良好

## 关键技术细节

### AgentRunner集成策略

由于agent.py已经实现，需要非侵入式集成：

```python
class AgentRunner(BaseRunner):
    def run(self, test_case: TestCase) -> RunResult:
        # 导入agent模块
        from agent import build_agent_graph, AgentState

        # 准备初始状态
        initial_state = AgentState(
            user_input=test_case.description,
            dsl_code="",
            error_log="",
            retry_count=0,
            is_success=False,
            instructions="",
            retrieved_docs=""
        )

        # 执行agent（包装计时）
        start_time = time.time()
        graph = build_agent_graph()
        final_state = graph.invoke(initial_state)
        total_time = time.time() - start_time

        # 提取结果
        return RunResult(
            test_id=test_case.id,
            method="agent",
            success=final_state["is_success"],
            assembly=final_state["instructions"],
            timing={"total": total_time},
            llm_usage=self._extract_llm_usage(final_state),
            metadata={"retry_count": final_state["retry_count"]}
        )
```

### DirectLLMRunner Prompt设计

```python
system_prompt = """You are an expert in RISC-V assembly programming.
Generate RISC-V assembly instructions that satisfy the given constraints.

IMPORTANT:
1. Output format: "0: addi x1 x2 10" (index: mnemonic operands)
2. Generate ONLY instructions (one per line)
3. Satisfy ALL constraints exactly
4. No comments or labels
"""

user_prompt = f"""Generate instructions for:
{test_case.description}

Output format example:
0: addi x1 x2 10
1: addi x3 x4 20
...
"""
```

### 约束验证逻辑

```python
def check_constraints(instructions, expected):
    violations = 0

    # 检查数量
    if len(instructions) != expected['count']:
        violations += 1

    # 检查类型
    expected_types = set(expected['instruction_types'])
    for instr in instructions:
        if instr['mnemonic'] not in expected_types:
            violations += 1

    # 检查寄存器范围
    for instr in instructions:
        for reg_name, (min_val, max_val) in expected['register_ranges'].items():
            if reg_name in instr['registers']:
                reg_val = instr['registers'][reg_name]
                if not (min_val <= reg_val < max_val):
                    violations += 1

    return violations
```

## 公平性保证

### 控制变量
- 相同的LLM模型（GPT-4o或配置中指定的模型）
- 相同的temperature（0.0确保可重复性）
- 相同的测试用例描述
- 相同的超时阈值
- 相同的评估标准

### 方法B变体
测试两个配置：
- **B1 (no_docs)**: 无API文档，测试LLM的内在知识
- **B2 (with_docs)**: 提供约束文档，模拟完美RAG

### 统计有效性
- 每个测试用例运行3次
- 报告均值、标准差、置信区间
- 使用配对t检验比较方法

## 输出示例

### CSV格式
```csv
test_id,difficulty,method,success,correctness_score,constraint_satisfaction,total_time,llm_calls,retry_count,cost,failure_mode
simple_01,simple,method_a,True,0.950,0.950,2.34,1,0,$0.0012,
simple_01,simple,method_b,True,0.850,0.800,0.45,1,0,$0.0008,
...
```

### Markdown报告片段
```markdown
# RVProbe Agent Benchmark Report

## Executive Summary

### Method A (Full Agent)
- **Overall Success Rate**: 92.3%
- **Average Time**: 3.45s
- **Total Cost**: $0.0567
- **Average Correctness Score**: 0.921

### Method B (Direct LLM)
- **Overall Success Rate**: 78.5%
- **Average Time**: 0.67s
- **Total Cost**: $0.0234
- **Average Correctness Score**: 0.812

## Method Comparison

| Metric | Method A | Method B | Winner |
|--------|----------|----------|--------|
| Success Rate | 92.3% | 78.5% | **Method A** |
| Avg Time (s) | 3.45 | 0.67 | **Method B** |
| Total Cost ($) | $0.0567 | $0.0234 | **Method B** |

...
```

## 验证清单

完成后需验证：

- [ ] 所有15个测试用例都能执行
- [ ] 两个方法都能运行每个测试用例
- [ ] 正确性评估合理（人工抽查5个结果）
- [ ] 时间测量准确（与手动计时对比）
- [ ] 成本估算符合实际API定价
- [ ] 生成的图表清晰可读
- [ ] Markdown报告格式正确
- [ ] CSV数据可导入Excel/Pandas

## 风险与缓解

| 风险 | 影响 | 缓解措施 |
|------|------|----------|
| Agent执行失败 | 无法完成对比 | 跳过失败用例，标记为timeout |
| LLM API限流 | 执行中断 | 添加重试逻辑，指数退避 |
| 汇编解析失败 | 无法评估 | 容错处理，标记为invalid_assembly |
| 内存不足 | 程序崩溃 | 顺序执行，避免并行 |

## 实现优先级

**必须实现**（核心功能）：
1. ✅ 测试用例定义（15个）
2. ✅ AgentRunner（方法A）
3. ✅ DirectLLMRunner（方法B）
4. ✅ AssemblyParser
5. ✅ ConstraintChecker
6. ✅ Benchmark orchestrator
7. ✅ CSV输出

**应该实现**（增强功能）：
1. 可视化图表
2. Markdown报告
3. 统计分析

**可以实现**（nice-to-have）：
1. 并行执行
2. 实时进度条
3. 交互式结果浏览

## 关键文件路径

### 需要创建的文件（按优先级）

1. **`rvprobe/agent/benchmark/test_suite/test_cases.py`** - 测试用例定义（最高优先级）
2. **`rvprobe/agent/benchmark/runners/agent_runner.py`** - 方法A执行器
3. **`rvprobe/agent/benchmark/runners/direct_llm_runner.py`** - 方法B执行器
4. **`rvprobe/agent/benchmark/evaluators/assembly_parser.py`** - 汇编解析
5. **`rvprobe/agent/benchmark/evaluators/constraint_checker.py`** - 约束验证
6. **`rvprobe/agent/benchmark/benchmark.py`** - 主编排器

### 需要读取的现有文件

- `rvprobe/agent/agent.py` - 理解agent接口
- `rvprobe/agent/rag.py` - 可能用于文档检索
- `rvprobe/agent/.env` - LLM配置

## 预期成果

完成后将得到：

1. **科学的对比数据**
   - 15个测试用例 × 2种方法 = 30个数据点
   - 3次重复 = 90个总测量值
   - 统计显著性检验

2. **可视化结果**
   - 5张高质量图表（PNG, 300dpi）
   - 成功率、时间、成本、失败模式

3. **详细报告**
   - Markdown格式，适合论文/文档引用
   - 执行摘要、详细分析、建议

4. **可复现性**
   - 配置文件记录所有参数
   - CSV数据可重新分析
   - 代码可重新运行

## 时间估算

- **Phase 1**: 3天（基础框架 + 测试用例）
- **Phase 2**: 4天（两个执行器）
- **Phase 3**: 3天（评估器）
- **Phase 4**: 2天（编排器）
- **Phase 5**: 3天（可视化 + 报告）

**总计**: 约3周（15个工作日）

---

*此计划设计为模块化、可扩展的benchmark系统，适用于学术论文或技术报告。*
