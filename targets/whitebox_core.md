# ChaosVM 白盒安全性定理（代数核心）

## 白盒攻击模型

攻击者拥有：
1. 完整字节码 `(c0_i, α_i, e_i)`
2. 完整三表 `(T_σ, T_C, T_D)` 及 G mixing configs
3. 全部 9 组 Q avalanche 参数
4. 可观察任意多次执行轨迹（寄存器和 `z_fields`）
5. 可选择任意输入

攻击者**不能获得**：`K_build`（构建期密钥）

## 要证明的四个不可行性

### 定理 A：份额不可缺性（Algebraic Incompressibility）

```
∀ i: decode(c0_i, a_i, c2_i, σ, DDM) = Φ_B(op_i)
但是：
  decode(c0_i, 0, c2_i, σ, DDM) ≠ Φ_B(op_i)  ∀ 零化的份额
  decode(c0_i, a_i, 0, σ, DDM) ≠ Φ_B(op_i)
  decode(0, a_i, c2_i, σ, DDM) ≠ Φ_B(op_i)
```

含义：三个份额任何一个被移除/清零，opcode 恢复失效。
→ 字节码在 3 个独立维度上编码，不可压缩为 1 维。

**现状**：T08 证明了全管道恢复 op = u。缺口是需要证明"缺失任一共享 → 恢复失败"。

### 定理 B：状态全链纠缠（Algebraic Entanglement）

```
∀ step t:
  H_{t+1} = Q_H(H_t ⊕ digest(op_t) ⊕ rotl(result_t,17) ⊕ edge_t ⊕ mem_t ⊕ call_t ⊕ spawn_t ⊕ ent_mix_t)
  Δ_σ 依赖于 z_t_hi ⊕ H_{t+1}
  Δ_C 依赖于 rotl(z_t_lo,23) ⊕ H_{t+1}
  Δ_D 依赖于 z_t_lo + z_t_hi ⊕ H_{t+1}
  
性质：∀ step t, ∀ i (1 ≤ i < t):
  σ_t ≠ σ'_t → σ_{t+1} ≠ σ'_{t+1}
  （确定性级联：前序任意差异 ⇒ 后续全链发散）
```

含义：不存在"跳过中间步骤直接跳到目标状态"的捷径。
→ 攻击者不能通过局部观察推断全局状态。

**现状**：T13（Init 发散）已证明。T14（步态级联）待证明。

### 定理 C：G 混合器熵覆盖（Entropy Distribution）

```
∀ (z_lo, z_hi) ∈ ℤ₂₅₆²:
  ∃ (x,y,w), gRounds(x,y,w,cfg) = (z_lo, z_hi)
  ∧ 3 轮 ARX 的复合是 (x,y,w) 上的置换

推论：输出空间 ℤ₂₅₆² 被完全覆盖
      → 无输出值被"偏好"，无统计偏差可用于逆向
```

**现状**：T07a（轮置换）+ T07b（输出满射）已证明。

### 定理 D：密钥恢复的代数障碍（No Algebraic Key Recovery）

```
∀ K_build:
  (T_σ, T_C, T_D) = XOF(K_build, func_id, table_seed)
  Q_σ/Q_C/Q_D/Q_H = XOF(K_build, func_id, q_seed)
  
属性：给定 (T_σ, T_C, T_D, Q_σ, Q_C, Q_D, Q_H, bytecode)，
      不存在代数算法恢复 K_build。
```

这是一个**密码学假设**（XOF 是安全的单向函数），
不是一个可以在 Lean 中证明的定理。
但我们可以证明：如果 K_build 未知，则初始化状态 (σ₀, CFA₀, DDM₀, H₀)
不确定 → 整条轨迹不确定 → opcode 恢复依赖于未知状态。

## 在 Lean 中可证明的部分

| 定理 | Lean 可证明？ | 重要性 |
|------|-------------|--------|
| A: 份额不可缺 | ✅ 需要新增 "缺失份额 → decode 错误" 引理 | 高 |
| B: 状态全链纠缠 (T14) | ✅ 归纳法 + 确定型 | 高 |
| C: G 混合器熵覆盖 | ✅ T07a + T07b 已完成 | 中 |
| D: 密钥恢复障碍 | ❌ 需密码学假设 | — |
| aInv 存在性 (T01) | ✅ 已完成 | 基础 |
| bridge+decode 不变性 (T08) | ✅ 已完成 | 基础 |

## 行动项

1. **定理 A 补充**：对 `encode_c0_i41/bridge_i41/decode_i41` 添加"零化任一共享 → decode ≠ Φ(op)" 证明
2. **定理 B 证明（T14）**：归纳法证明"step 0 有差异 → 所有后续 step 有差异"
3. 定理 C 已完成
4. 定理 D 应记录为密码学假设（不可在 Lean 中证明）
