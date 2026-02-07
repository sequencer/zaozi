# LLM API 配置指南

## 快速开始

### 1. 配置环境变量

编辑 `/home/clo91eaf/Project/zaozi/rvprobe/agent/.env` 文件：

```bash
# 必需的环境变量
LLM_API_KEY=your-api-key-here
LLM_API_BASE=https://api.your-provider.com/v1
LLM_MODEL=model-name
```

### 2. 更新 benchmark 配置（可选）

如果需要为benchmark指定特定模型，编辑 `benchmark/config.yaml`：

```yaml
llm_model: "Qwen/Qwen2.5-Coder-32B-Instruct"  # 使用你的模型名称
llm_temperature: 0.0
llm_max_tokens: 4000
```

### 3. 验证配置

```bash
cd /home/clo91eaf/Project/zaozi/rvprobe/agent
uv run python -c "import os; from dotenv import load_dotenv; load_dotenv(); print('API Key:', os.getenv('LLM_API_KEY')[:20]+'...'); print('API Base:', os.getenv('LLM_API_BASE')); print('Model:', os.getenv('LLM_MODEL'))"
```

## 配置方式详解

### 方式1：使用 .env 文件（推荐）

**优点**：
- 安全（不会提交到git）
- 集中管理所有环境变量
- 支持多环境切换

**配置步骤**：

1. 从示例复制：
   ```bash
   cp .env.example .env
   ```

2. 编辑 `.env` 文件，填入你的凭证：
   ```bash
   LLM_API_KEY=sk-your-actual-api-key
   LLM_API_BASE=https://api.siliconflow.cn/v1
   LLM_MODEL=Qwen/Qwen2.5-Coder-32B-Instruct
   ```

3. 确保 `.env` 在 `.gitignore` 中（已配置）

### 方式2：使用系统环境变量

```bash
export LLM_API_KEY="your-api-key"
export LLM_API_BASE="https://api.siliconflow.cn/v1"
export LLM_MODEL="Qwen/Qwen2.5-Coder-32B-Instruct"

# 然后运行
uv run benchmark/benchmark.py
```

### 方式3：临时覆盖

```bash
LLM_MODEL="deepseek-ai/DeepSeek-V2.5" uv run benchmark/benchmark.py --tests TC-S01
```

## 常见LLM服务配置

### 🔵 OpenAI (官方)

```bash
LLM_API_KEY=sk-proj-...
LLM_API_BASE=https://api.openai.com/v1
LLM_MODEL=gpt-4o
```

**成本参考**（更新到 config.yaml）：
```yaml
prompt_token_cost: 0.0025      # $2.50 per 1M tokens
completion_token_cost: 0.010   # $10.00 per 1M tokens
```

### 🟢 SiliconFlow（当前使用）

```bash
LLM_API_KEY=sk-...
LLM_API_BASE=https://api.siliconflow.cn/v1
LLM_MODEL=Qwen/Qwen2.5-Coder-32B-Instruct
```

**可用模型**：
- `Qwen/Qwen2.5-Coder-32B-Instruct` - 适合编程任务
- `Qwen/Qwen2.5-72B-Instruct` - 更大模型
- `deepseek-ai/DeepSeek-V2.5` - DeepSeek模型

**成本参考**：查看 [SiliconFlow定价](https://siliconflow.cn/pricing)

### 🟣 DeepSeek

```bash
LLM_API_KEY=sk-...
LLM_API_BASE=https://api.deepseek.com/v1
LLM_MODEL=deepseek-coder
```

### 🔴 本地模型（Ollama）

```bash
LLM_API_BASE=http://localhost:11434/v1
LLM_MODEL=qwen2.5-coder:32b
LLM_API_KEY=not-needed
```

**前置条件**：
```bash
# 安装并启动 Ollama
ollama serve

# 拉取模型
ollama pull qwen2.5-coder:32b
```

### 🟡 Azure OpenAI

```bash
LLM_API_KEY=your-azure-key
LLM_API_BASE=https://your-resource.openai.azure.com/
LLM_MODEL=gpt-4
```

### 🟠 Anthropic Claude

```bash
LLM_API_KEY=sk-ant-...
LLM_API_BASE=https://api.anthropic.com/v1
LLM_MODEL=claude-3-opus-20240229
```

## 环境变量优先级

系统支持两套命名方式，优先级如下：

```
LLM_API_KEY > OPENAI_API_KEY
LLM_API_BASE > OPENAI_API_BASE
LLM_MODEL > config.yaml中的llm_model
```

## 成本追踪配置

在 `benchmark/config.yaml` 中更新成本信息：

```yaml
# Cost Calculation (USD per 1M tokens)
prompt_token_cost: 0.0025      # 输入token成本
completion_token_cost: 0.010   # 输出token成本
```

**如何查找定价**：
1. 访问你的LLM服务商定价页面
2. 找到每1M token的价格（通常以USD计）
3. 将价格除以1,000,000得到每token成本
4. 更新到配置文件

**示例计算**（GPT-4o）：
- 输入：$2.50 per 1M tokens → `0.0025`
- 输出：$10.00 per 1M tokens → `0.010`

## 测试配置

### 快速测试 LLM 连接

```bash
cd /home/clo91eaf/Project/zaozi/rvprobe/agent

# 测试环境变量
uv run python -c "import os; from dotenv import load_dotenv; load_dotenv(); print('✓ API configured' if os.getenv('LLM_API_KEY') else '✗ API key missing')"

# 测试 agent 的 LLM 连接
uv run python -c "from agent import build_agent_graph; print('✓ Agent can be built')"
```

### 运行简单测试

```bash
# 运行最简单的测试用例
uv run benchmark/benchmark.py --tests TC-S01

# 检查结果
cat benchmark_results/REPORT.md
```

## 故障排除

### 问题1：API Key not found

**错误**：`No API key provided` 或类似

**解决**：
```bash
# 检查 .env 文件是否存在
ls -la .env

# 检查环境变量是否加载
uv run python -c "import os; from dotenv import load_dotenv; load_dotenv(); print(os.getenv('LLM_API_KEY'))"
```

### 问题2：Connection refused

**错误**：`Connection refused` 或 `Unable to connect`

**解决**：
1. 检查 API Base URL 是否正确
2. 检查网络连接
3. 验证 API 服务是否可访问：
   ```bash
   curl -I https://api.siliconflow.cn/v1
   ```

### 问题3：Model not found

**错误**：`Model not found` 或 `Invalid model`

**解决**：
1. 验证模型名称拼写
2. 检查该模型是否在你的服务商可用
3. 查看服务商文档获取可用模型列表

### 问题4：成本统计不准确

**解决**：
更新 `config.yaml` 中的 token 成本为实际定价：
```yaml
prompt_token_cost: 0.001      # 更新为实际价格
completion_token_cost: 0.002  # 更新为实际价格
```

## 安全最佳实践

1. ✅ **使用 .env 文件**存储凭证
2. ✅ **确保 .env 在 .gitignore 中**
3. ✅ **不要在代码中硬编码 API key**
4. ✅ **定期轮换 API keys**
5. ✅ **为不同环境使用不同的 keys**
6. ✅ **使用只读或受限权限的 keys**

## 多环境配置

### 开发环境

```bash
# .env.development
LLM_API_KEY=sk-dev-...
LLM_MODEL=Qwen/Qwen2.5-Coder-32B-Instruct
```

### 生产环境

```bash
# .env.production
LLM_API_KEY=sk-prod-...
LLM_MODEL=gpt-4o
```

### 切换环境

```bash
# 使用开发环境
cp .env.development .env

# 使用生产环境
cp .env.production .env
```

## 参考链接

- [SiliconFlow API文档](https://docs.siliconflow.cn/)
- [OpenAI API文档](https://platform.openai.com/docs/api-reference)
- [DeepSeek API文档](https://platform.deepseek.com/api-docs/)
- [Anthropic API文档](https://docs.anthropic.com/)
- [Ollama文档](https://ollama.ai/docs)
