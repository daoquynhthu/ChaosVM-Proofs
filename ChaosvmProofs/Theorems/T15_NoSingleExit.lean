/-! # T15: 无单一出口架构性质 (No Single Exit)

## 定理陈述

ChaosVM 反篡改设计遵守**无单一出口**原则：所有抗篡改机制仅通过累积投毒
（accumulative poison）实现，从不使用 `if(check) exit(1)` 或等价的一次性检查。

## 证明方式

这不是一个数学定理，而是通过代码审计验证的架构性质。具体审计范围：

1. **P_σ / P_C / P_D 投毒通道** (`anti_tamper/sensors.rs`):
   - 所有传感器仅向 three PoisonAccumulator 累加值，从不触发条件分支
   - `run_all_sensors` → `PoisonAccumulator { poison_sigma, poison_cfa, poison_ddm }`

2. **Init 投毒吸收** (`init.rs`):
   - `init_poisoned` 将 P 值异或入 σ₀/CFA₀/DDM₀/H₀，不执行任何 `exit`/`abort`
   - 参见 `Definitions/Init.lean` 的 `init_poisoned` 定义

3. **级联发散**:
   - 投毒仅在 100-500 步后表现为静默错误结果，无即时崩溃
   - 形式化模型参见 T13 (Init 发散) 和 T14 (投毒级联)

4. **Rust 源码审计** (`chaosvm-core/src/conj_vm/`):
   - `exec.rs`: `step()` 从不检查 poison 值；poison 只通过状态影响后续计算
   - `anti_tamper/`: 所有传感器只读，无写入/退出操作
   - `init.rs`: `init_poisoned` 无条件分支退出

## 依赖

架构审计已验证完毕。无 Lean 形式化证明。
-/
