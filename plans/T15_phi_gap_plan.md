# T15 形式化 + phi_op_inv Gap 闭包 — 补强计划

## 问题

### Gap 1: T17 安全边界偏移
T17 证明 `v_t` 与运行时状态 (σ, DDM, c1_t) 无关。这是编码方案代数消去（每次 XOR 抵消）的直接结果。  
但 Rust 实现中，`v_t` 经过 `phi_op_inv` 置换后才成为实际 opcode。**Lean 模型未覆盖 `phi_op_inv` 层。**

```
Lean 模型:  c0 → bridge → decode → v_t
Rust 实现:  c0 → bridge → decode → v_t → phi_op_inv → op_u8 → execute
                                     ^^^^^
                                     安全边界在此
```

### Gap 2: T15 无 Lean 证明
T15（无单一出口）目前是纯文档，形式上说没有一个 Lean 定理来确保 `init`/`init_poisoned` 永不产生 `exit` 等价语义。

---

## 总目标

| 层 | 内容 | 工作量 |
|----|------|--------|
| **L1** | 补齐 `phi_op_inv` 模型 → 重述 T17 | 2–3h |
| **L2** | 在 decode 中引入状态依赖非线性项 → 打破 XOR 对称 | 4–6h |
| **L3** | T15 形式化（可选） | 3–5h |

---

## L1: phi_op_inv 模型补齐

### 1.1 新建 Definitions/PhiPerm.lean

定义 build-time opcode 置换：

```lean
/-- phi: 原始 opcode → 编码 opcode (u = phi[op])。build-time 随机生成的双射。 -/
def phi (op : Nat) : Nat := ...

/-- phi_op_inv: u → 原始 opcode。phi 的逆置换。 -/
def phi_op_inv (u : Nat) : Nat := ...

theorem phi_bijective : Function.Bijective phi := ...
theorem phi_inv_correct (op : Nat) : phi_op_inv (phi op) = op := ...
```

实现方式：
- `phi` 用 `dec_trivial` 生成（256 项 Fin 256 → Fin 256 置换表）
- `phi_op_inv` 用同样的表反向查找
- 或者简化为随机种子驱动的 `qAvalanche` 排列（更符合 Rust 实际）

### 1.2 修改 T17

新增 `decode_full` 包装 `decode_i41` + `phi_op_inv`：

```lean
def decode_full (c0_eff c1_t c2 σ DDM : Nat) 
    (q_sigma q_ddm : QAvalancheConfig) : Nat :=
  phi_op_inv (decode_i41 c0_eff c1_t c2 σ DDM q_sigma q_ddm)
```

重述 T17：

```lean
theorem T17_functional_equivalence_full (st₁ st₂ : VmState) 
    (insns : List InsnRuntime) (ctx : ProgramContext) :
    (map decode_full (run_program_core st₁ insns ctx).snd) = 
    (map decode_full (run_program_core st₂ insns ctx).snd) := ...
```

### 1.3 更新依赖定理

- T08 `bridge_decode_invariant`：更新为 `decode_full(bridge(encode(u))) = op`（其中 `u = phi op`）
- K3：`bridge` 输出仍随状态变化；确认 `phi_op_inv` 不影响该性质

### 1.4 更新审计报告

在 `targets/audit_report.md` 中记录 Gap 已闭合并更新依赖图。

---

## L2: 打破 XOR 对称性（Rust + Lean）

### 2.1 修改 decode_i41（Rust）

在 `decode_i41` 中添加一项 `bridge` 无法镜像的 σ 依赖：

```rust
pub fn decode_i41(c0_eff, c1_t, c2, sigma, ddm, q_sigma, q_ddm) -> u8 {
    let base = c0_eff ^ permute(c1_t, sigma, q_sigma) ^ permute(c2, ddm, q_ddm);
    // 第 4 项：rotl(P(c1_t, σ), σ_lo) — bridge 没有对应的取消项
    let extra = permute(c1_t, sigma, q_sigma).rotate_left(sigma as u32 & 7);
    base ^ extra
}
```

此时 `v_t = u ⊕ rotl(P(c1_t, σ), σ_lo)`，T17 `v_t` 不变性不再成立。

### 2.2 对应修改 Lean decode_i41

保持语义一致。

### 2.3 更新 T16/T17/K3

所有依赖 `decode_i41` 的证明需要：
- `bridge_decode_invariant`：不再成立（`v_t ≠ u`），需要新不变式
- T16：`decode_full`（含 `phi_op_inv` 补偿）的不变性仍然需要证明
- T17：`decode_full` 版本的输出独立于状态仍需成立
- K3：`bridge_i41` 不受影响

**核心观察**：`phi_op_inv` 现在需要补偿第 4 项：

```
phi_op_inv 不再只是静态置换，而是运行时可计算的函数：
op_u8 = phi_inv_compensated[v_t, σ, c1_t, q_sigma]
```

如果采用这种方式，`phi_op_inv` 变为依赖状态的函数，T17 需要重新表述。

### 2.4 Rust IR 发射器更新

`emit_decode_i41` 增加第 4 项 LLVM IR 发射。

---

## L3: T15 形式化（可选）

### 3.1 定义 NoExit typeclass

```lean
class NoExit (α : Type) where
  /-- 所有产生 α 值的方式都不包含 `exit` 等价语义。 -/
  no_exit : α → Prop

instance : NoExit Nat where
  no_exit _ := True  -- Nat 构造不含 exit

instance : NoExit (σ × CFA × DDM × H) where
  no_exit (σ, CFA, DDM, H) := True  -- 元组构造不含 exit
```

### 3.2 证明 init / init_poisoned 无 exit

```lean
theorem init_no_exit (k0 k1 r0 r1 : Nat) 
    (qσ qC qD qH : QAvalancheConfig) : True :=
  trivial  -- init 只做算术，无 exit

theorem init_poisoned_no_exit (k0 k1 r0 r1 : Nat)
    (qσ qC qD qH : QAvalancheConfig)
    (salt p_σ p_C p_D : Nat) : True :=
  trivial  -- init_poisoned 同
```

### 3.3 更新 T15 文档

T15 从纯文档升级为包含上述定理的证明文件。

---

## 依赖关系

```
L1 ─→ L2（可并行开始，但 L2 依赖 L1 的 phi 模型）
L1 ─→ L3（独立）
L2 ─→ T08/T16/T17/K3（需大量修改）
```

## 风险

| 风险 | 概率 | 影响 | 缓解 |
|------|------|------|------|
| L2 使 decode 正确性证明不成立 | 高 | 需要新的不变式 | L2 延期，先做 L1+L3 |
| `phi_op_inv` 在 Rust 中可能是动态计算而非静态表 | 中 | 模型需更复杂 | 先做静态模型，后续扩展 |
| L2 的 LLVM IR 发射增加每步开销 | 中 | 性能下降 | 只对 secure preset 启用 |

## 推荐执行顺序

1. ✅ **L1.1–L1.2**: `PhiPerm.lean` + T17 重述（2–3h）
2. ⏳ **L1.3–L1.4**: 更新依赖定理 + 审计报告（0.5h）
3. ❓ **评估**: L1 完成后再决定是否执行 L2（需要 Rust 团队参与）
4. ❓ **T15**: 优先级最低，可推迟
