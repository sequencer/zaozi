**系统/角色定义：**
你是一位专精于 **神经符号 AI (Neuro-Symbolic AI)** 和 **硬件验证** 的资深软件架构师。你擅长使用 **Python (LangGraph)** 和 **Scala 3 (Mill Build Tool)** 构建自动化系统。

**任务：**
我需要你为 **"RVProbe Agent"** 实现核心的基础设施。这是一个自动化的验证生成器。它将自然语言意图转化为 Scala DSL 约束代码，并通过 SMT 求解器进行验证。


**系统架构与约束：**

1. **核心理念：**
* **生成即代码 (Generation as Code)：** LLM 生成 Scala 3 DSL 代码，而不是直接生成汇编。
* **编译反馈闭环 (Compiler-in-the-Loop)：** 系统利用 Scala 编译器 (`mill`) 和 SMT 求解器的执行结果作为反馈。如果代码有错或逻辑不可满足 (UNSAT)，Agent 会自动重试并修复。

2. **架构分层：**
* **控制平面 (Python)：** 使用 **LangGraph** 管理状态机（检索 -> 生成 -> 执行 -> 决策）。
* **数据平面 (Scala)：** 一个标准的 **Mill** 项目。Agent 将生成的代码写入指定文件，通过运行 Mill 任务来执行验证。

3. **工作流逻辑 (简化版)：**
* **检索 (Retrieve)：** Mock 返回一些 DSL API 文档作为上下文。
* **生成 (Generate)：** LLM 根据上下文生成 Scala DSL 代码。
* **执行 (Execute)：**
1. 参考 `rvprobe/src/agent/Template.scala` Python 将代码写入 `rvprobe/src/agent/Test.scala`。
2. 执行命令 `mill rvprobe.runMain me.jiuyang.rvprobe.agent.Test out/test.bin`
3. 捕获输出。如果包含 "Error" 或 "UNSAT"，返回失败状态；如果包含正常的指令序列，返回成功状态。

* **决策 (Decide)：**
* 成功 -> 结束 (End)。
* 失败 -> 带着错误日志跳回 "生成" 步骤 (最多重试 3 次)。

**实现要求：**

请生成以下项目结构和代码文件。代码需要简洁、模块化。

**1. 项目结构：**
在 `rvprobr/agent` 目录中编写对应的python代码

**2. Python Agent 实现 (`agent.py`)：**

* **技术栈：** `langgraph`, `langchain_openai`, `subprocess`。
* **状态定义 (State)：** 包含 `user_input`, `dsl_code`, `error_log`, `retry_count`, `is_success`。
* **节点实现：**
* `retrieve_node`：返回模拟的 API 文档。
* `generate_node`：构建 Prompt，生成 Scala 代码。**注意：Prompt 需要包含将代码包裹在 Scala `object/main` 结构中的指令，或者由 Python 代码负责包裹。**
* `execute_node`：写入文件 -> 运行 Mill -> 解析结果。


* **图构建：** 使用 `StateGraph`。核心是 `execute` 之后的条件边：如果失败且 `retry < max`，则指向 `generate`；否则指向 `END`。

**LLM 上下文设定：**

* 假设 DSL API 包含 `isAddi()`, `rdRange(min, max)` 等。
* 使用 `gpt-4o` 作为模型占位符。

**交付产物**

最后要求交付一个python agent系统:
* 将一系列对指令的自然语言描述的约束要求输入给python 脚本后输出包含约束的Test.scala文件和最终的指令序列
* Test.scala文件可以正常运行
* 指令序列符合自然语言描述
* 如果找不到符合约束的指令序列则返回不满足