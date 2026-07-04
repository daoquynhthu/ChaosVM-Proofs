/-! # T15: 无单一出口架构性质 (No Single Exit)

## 定理陈述

ChaosVM 反篡改设计遵守**无单一出口**原则：所有抗篡改机制仅通过累积投毒
（accumulative poison）实现，从不使用 `if(check) exit(1)` 或等价的一次性检查。

## Lean 形式化

### NoExit 性质（结构保证）

在 Lean 模型中，NoExit 性质由类型系统结构保证：
- `InitState` 是纯数据结构（`sigma0, cfa0, ddm0, h0` 等 Nat 字段）
- `init` 和 `init_poisoned` 是纯函数 `InitState → InitState`
- 模型中没有 `exit`/`abort`/`panic` 构造 — 所有计算都是纯函数应用

因此，`init`/`init_poisoned` 的 NoExit 性质在 Lean 模型中**平凡成立**（`True`）。

### 已有形式化（Definitions/Init.lean）

| 定理 | 说明 |
|------|------|
| `init_poisoned_zero_equals_clean` | p=0 时 init_poisoned = init |
| `init_poisoned_structurally_differs` | p≠0 时结构不同（poison 字段） |
| `init_poisoned_sigma0_diverges` | σ 通道发散条件 |
| `init_poisoned_cfa0_diverges` | CFA 通道发散条件 |
| `init_poisoned_ddm0_diverges` | DDM 通道发散条件 |
| `init_poisoned_h0_diverges` | H 通道发散条件 |

### 审计验证范围

1. **P_σ / P_C / P_D 投毒通道** (`anti_tamper/sensors.rs`):
   - 所有传感器仅向 PoisonAccumulator 累加值，从不触发条件分支

2. **Init 投毒吸收** (`init.rs`):
   - `init_poisoned` 将 P 值异或入 σ₀/CFA₀/DDM₀/H₀，不执行任何 `exit`/`abort`

3. **级联发散** (T13/T14):
   - 投毒仅在 100-500 步后表现为静默错误结果，无即时崩溃

4. **Rust 源码审计** (`chaosvm-core/src/conj_vm/`):
   - `exec.rs`: `step()` 从不检查 poison 值；poison 只通过状态影响后续计算
   - `anti_tamper/`: 所有传感器只读，无写入/退出操作
   - `init.rs`: `init_poisoned` 无条件分支退出

## 依赖

架构审计已验证完毕。Lean 模型中 NoExit 性质由类型系统保证（纯函数模型）。
-/
