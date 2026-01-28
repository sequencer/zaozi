# RVProbe Agent

自动化验证生成器，将自然语言约束转化为 Scala DSL 代码并生成 RISC-V 指令序列。

## 项目架构

- **控制平面 (Python)**: 使用 LangGraph 管理状态机工作流
- **数据平面 (Scala)**: 使用 Mill 构建工具和 SMT 求解器进行验证
- **编译反馈闭环**: 自动重试和修复编译错误

## 安装依赖

```bash
cd rvprobe/agent
pip install -r requirements.txt
```

## 配置

1. 复制环境变量模板：
```bash
cp .env.example .env
```

2. 编辑 `.env` 文件，填入你的 OpenAI API Key：
```
OPENAI_API_KEY=sk-...
```

## 使用方法

### 命令行运行

```bash
# 使用默认示例
python agent.py

# 自定义约束
python agent.py "Generate 10 ADDI instructions with rd in range 1-10"
```

### Python 脚本调用

```python
from agent import run_agent

result = run_agent("Generate 20 SLLI instructions for RV64I")

if result['is_success']:
    print(result['instructions'])
else:
    print(result['error_log'])
```

## 示例

### 示例 1: 简单约束
```bash
python agent.py "Generate 20 ADDI instructions where rd and rs1 are both in range 1-31"
```

### 示例 2: 多种指令类型
```bash
python agent.py "Generate 10 arithmetic instructions: 5 ADDI and 5 ADDW with different register ranges"
```

### 示例 3: 带立即数约束
```bash
python agent.py "Generate 15 SLLI instructions with shift amount (immediate) between 0 and 10"
```

## 工作流程

```
用户输入自然语言约束
        ↓
[Retrieve] 获取 DSL API 文档
        ↓
[Generate] LLM 生成 Scala DSL 代码
        ↓
[Execute] 写入 Test.scala → 运行 Mill → 解析输出
        ↓
    成功? ──Yes→ 返回指令序列
        |
       No (有错误)
        ↓
    重试次数 < 3? ──Yes→ 带错误信息重新 Generate
        |
       No
        ↓
    返回失败和错误日志
```

## 输出文件

- **Test.scala**: 生成的 Scala DSL 代码 (`rvprobe/src/agent/Test.scala`)
- **test.bin**: 编译后的指令二进制文件 (`out/test.bin`)

## 架构说明

### 状态机节点

1. **Retrieve**: Mock 返回 DSL API 文档
2. **Generate**: 使用 GPT-4 生成 Scala DSL 代码
3. **Execute**: 执行编译和验证流程

### 决策逻辑

- 成功 → 结束并返回结果
- 失败且重试次数 < 3 → 带错误信息回到 Generate
- 失败且达到最大重试次数 → 结束并返回错误

### DSL API 示例

```scala
object test extends RVGenerator:
  val sets = isRV64GC()
  def constraints() =
    (0 until 20).foreach { i =>
      instruction(i, isAddi()) {
        rdRange(1, 32) & rs1Range(1, 32) & immRange(0, 100)
      }
    }
```

## 故障排除

### Mill 命令失败
确保在项目根目录有正确的 Mill 配置，并且已安装 Mill 构建工具。

### OpenAI API 错误
检查 `.env` 文件中的 API Key 是否正确，确保有足够的配额。

### SMT Solver UNSAT
约束可能过于严格导致无解。尝试放宽约束条件或减少指令数量。

## 技术栈

- **Python**: LangGraph, LangChain, OpenAI API
- **Scala**: Mill Build Tool, SMT-LIB
- **AI**: GPT-4o (可配置其他模型)
