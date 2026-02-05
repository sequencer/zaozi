# RVProbe Benchmark - Complete Implementation ✅

完整实现了RVProbe Agent的benchmark框架，包含所有5个Phase的功能。

## ✅ 完整实施状态

### Phase 1-5 全部完成

**Phase 1**: 基础框架 ✅
- 测试用例定义（15个）
- 数据类Schema
- 配置系统

**Phase 2**: 执行器 ✅
- AgentRunner（方法A）
- DirectLLMRunner（方法B）

**Phase 3**: 评估器 ✅
- 汇编解析器
- 约束检查器
- 指标计算

**Phase 4**: 编排与执行 ✅
- 主编排器benchmark.py
- CLI接口
- 并行执行
- 结果导出（CSV/JSON）

**Phase 5**: 可视化与报告 ✅  
- 5种图表类型
- Markdown报告生成
- 统计分析（P50/P95/P99）
- 失败分析

### 核心文件

1. **[benchmark.py](benchmark.py)** - 主编排器
   - 配置加载（YAML）
   - 测试用例过滤
   - 顺序/并行执行
   - 结果收集和保存（CSV/JSON）
   - 命令行接口（CLI）
   - 进度报告

2. **[verify_phase4.py](verify_phase4.py)** - Phase 4 验证脚本
   - 测试所有核心功能
   - 验证数据序列化
   - 检查错误处理

### 功能特性

- ✅ 从YAML加载配置
- ✅ 测试用例过滤（按ID、难度）
- ✅ 支持顺序和并行执行
- ✅ 多次重复运行（统计有效性）
- ✅ CSV和JSON结果导出
- ✅ 实时进度显示
- ✅ 错误处理和超时管理
- ✅ 结果摘要打印

## 🚀 使用方法

### 前置要求

确保在`rvprobe/agent`目录下已安装所有依赖：

```bash
cd /home/clo91eaf/Project/zaozi/rvprobe/agent

# 安装核心依赖
uv sync

# 安装可视化依赖
uv pip install matplotlib numpy pandas
```

### 运行验证

```bash
# 验证Phase 4实现（编排器）
cd /home/clo91eaf/Project/zaozi/rvprobe/agent
uv run benchmark/verify_phase4.py

# 验证Phase 5实现（可视化）
uv run benchmark/verify_phase5.py
```

### 运行Benchmark

```bash
# 基础用法：运行所有测试
cd /home/clo91eaf/Project/zaozi/rvprobe/agent
uv run benchmark/benchmark.py

# 只运行简单测试
uv run benchmark/benchmark.py --difficulty simple

# 运行特定测试
uv run benchmark/benchmark.py --tests TC-S01 TC-S02

# 使用自定义配置
uv run benchmark/benchmark.py --config my_config.yaml

# 3次重复运行（统计分析）
uv run benchmark/benchmark.py --repetitions 3

# 并行执行（8个worker）
uv run benchmark/benchmark.py --parallel --workers 8

# 指定输出目录
uv run benchmark/benchmark.py --output-dir ./my_results
```

### CLI 参数

```
usage: benchmark.py [-h] [--config CONFIG] [--tests TESTS [TESTS ...]]
                    [--difficulty {simple,medium,complex}]
                    [--repetitions REPETITIONS] [--parallel]
                    [--workers WORKERS] [--output-dir OUTPUT_DIR]

选项:
  -h, --help            显示帮助信息
  --config, -c CONFIG   配置文件路径 (默认: config.yaml)
  --tests, -t TESTS     指定测试ID (例如: TC-S01 TC-S02)
  --difficulty, -d      按难度过滤 (simple/medium/complex)
  --repetitions, -r     重复次数 (覆盖配置文件)
  --parallel, -p        启用并行执行
  --workers, -w         并行worker数量
  --output-dir, -o      结果输出目录
```

## 📊 输出格式

### CSV 格式 (results_summary_YYYYMMDD_HHMMSS.csv)

包含每次测试运行的扁平化指标：

```csv
test_id,difficulty,method,success,correctness_score,total_time,llm_calls,cost,...
TC-S01,simple,agent,True,0.920,2.340,1,$0.0012,...
TC-S01,simple,direct_llm,True,0.850,0.450,1,$0.0008,...
```

### JSON 格式 (results_detailed_YYYYMMDD_HHMMSS.json)

完整的结构化结果，包含：
- 元数据（时间戳、配置）
- 每个结果的完整指标
- 原始输出和错误日志

```json
{
  "metadata": {
    "timestamp": "2026-02-05T16:53:57.348329",
    "config": {...},
    "total_results": 30
  },
  "results": [
    {
      "test_id": "TC-S01",
      "method": "agent",
      "success": true,
      "assembly": "...",
      "correctness": {...},
      "efficiency": {...},
      "robustness": {...}
    }
  ]
}
```

### 可视化图表 (PNG, 300dpi)

自动生成5种图表：

1. **success_rate_by_difficulty.png** - 按难度分组的成功率对比
2. **time_distribution.png** - 执行时间分布直方图
3. **cost_comparison.png** - API成本对比柱状图
4. **correctness_scores.png** - 正确性分数箱形图
5. **failure_modes.png** - 失败模式分布饼图

### Markdown报告 (REPORT.md)

包含6个主要部分：

1. **Executive Summary** - 执行摘要（成功率、时间、成本等）
2. **Method Comparison** - 方法对比表格（含赢家标注）
3. **Results by Difficulty** - 按难度细分的结果
4. **Performance Analysis** - 统计分析（P50/P95/P99）
5. **Failure Analysis** - 失败分析（失败模式统计）
6. **Recommendations** - 使用建议

## 🔧 配置说明

编辑 [config.yaml](config.yaml) 来自定义：

```yaml
# LLM设置
llm_model: "gpt-4o"
llm_temperature: 0.0
llm_max_tokens: 4000

# 执行设置
timeout_seconds: 300
max_retries: 3

# 统计有效性
num_repetitions: 1  # 改为3进行统计分析

# 并行执行
parallel_execution: false
max_workers: 4

# 输出设置
results_dir: "./benchmark_results"
save_raw_outputs: true

# 测试过滤
selected_tests: []  # 留空运行所有测试
difficulty_filter: []  # 留空运行所有难度
```

## 📁 结果目录结构

```
benchmark_results/
├── results_summary_20260205_165357.csv      # CSV摘要
├── results_detailed_20260205_165357.json    # JSON详细结果
├── success_rate_by_difficulty.png           # 成功率对比图
├── time_distribution.png                    # 时间分布图
├── cost_comparison.png                      # 成本对比图
├── correctness_scores.png                   # 正确性分数图
├── failure_modes.png                        # 失败模式图（如有失败）
├── REPORT.md                                # 综合分析报告
└── benchmark.log                            # 执行日志
```

## 🎉 完成状态

**所有5个Phase均已完成！** ✅

### 验证清单

- [x] Phase 1: 测试用例和数据类 (15个测试用例)
- [x] Phase 2: 执行器实现 (AgentRunner + DirectLLMRunner)
- [x] Phase 3: 评估器实现 (解析 + 验证 + 指标)
- [x] Phase 4: 编排器 (顺序/并行执行 + CLI + 导出)
- [x] Phase 5: 可视化 (5种图表 + Markdown报告)
- [x] 所有验证测试通过 (Phase 4: 7/7, Phase 5: 4/4)
- [x] 配置加载正常
- [x] 结果序列化（CSV/JSON）
- [x] 错误处理
- [x] 图表生成
- [x] 报告生成
- [x] 集成测试

### 可运行演示

```bash
cd /home/clo91eaf/Project/zaozi/rvprobe/agent

# 快速演示：运行单个简单测试
uv run benchmark/benchmark.py --tests TC-S01

# 查看生成的文件
ls -lh benchmark_results/

# 查看报告
cat benchmark_results/REPORT.md
```

### 框架特性

✅ **完整性** - 覆盖整个workflow：执行 → 评估 → 可视化 → 报告  
✅ **可扩展性** - 易于添加新的测试用例或方法  
✅ **可配置性** - YAML配置文件控制所有参数  
✅ **鲁棒性** - 完善的错误处理和日志记录  
✅ **可读性** - 清晰的代码结构和文档  
✅ **专业性** - 出版级图表和统计分析

## ❓ 关于Agent模块

**Q: agent模块是什么？**

A: [agent.py](../agent.py) 是Phase 2中实现的"方法A"核心，包含完整的工作流：
- RAG文档检索 (`rag.py`)
- LLM Scala DSL代码生成
- Mill编译执行
- Z3约束求解验证
- 自动重试机制

**Q: 为什么需要uv运行？**

A: agent模块依赖以下包（在 [pyproject.toml](../pyproject.toml) 中定义）：
- `langgraph` - 工作流编排
- `langchain-openai` - LLM接口
- `python-dotenv` - 环境变量
- `chromadb` - RAG向量数据库
- `sentence-transformers` - 文本嵌入

使用 `uv run` 确保在正确的虚拟环境中运行，所有依赖都可用。

**Q: 直接运行 python 会怎样？**

A: 如果不使用uv环境，会出现 `ModuleNotFoundError: No module named 'dotenv'` 等错误，因为系统Python环境中没有安装这些包。

## 🐛 故障排除

### 依赖问题

```bash
# 重新安装依赖
cd /home/clo91eaf/Project/zaozi/rvprobe/agent
uv sync --force

# 检查已安装的包
uv pip list
```

### 环境变量

确保 `.env` 文件包含必要的API密钥：

```bash
# 在 /home/clo91eaf/Project/zaozi/rvprobe/agent/.env
LLM_API_KEY=your-api-key
LLM_API_BASE=https://api.openai.com/v1
LLM_MODEL=gpt-4o
```

### 测试失败

```bash
# 运行单个简单测试进行调试
uv run benchmark/benchmark.py --tests TC-S01 --repetitions 1

# 查看详细日志
cat benchmark_results/benchmark.log
```

## 📝 验证清单

- [x] Phase 1: 测试用例和数据类定义
- [x] Phase 2: 执行器实现
- [x] Phase 3: 评估器实现
- [x] Phase 4: 编排器和CLI
- [x] Phase 5: 可视化和报告生成
- [x] 配置加载正常
- [x] 测试用例加载和过滤
- [x] Orchestrator初始化
- [x] 结果序列化（CSV/JSON）
- [x] 图表生成（5种类型）
- [x] Markdown报告生成
- [x] 错误处理
- [x] 摘要打印
- [x] CLI参数解析
- [x] 所有验证测试通过 (Phase 4: 7/7, Phase 5: 4/4)

---

**Benchmark Framework Status**: ✅ **COMPLETE - PRODUCTION READY**

🎉 所有Phase已完成，框架可用于生产环境！
