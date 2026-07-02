# 成本代数定理：规划文档

## 总体目标

证明四个代数性质，联合构成"攻击者必须模拟完整 VM"的下界论证。

```
K1: G混合器192bit置换 ──→ 混合阶段无熵损失，不可绕过 ✅
K2: H链顺序依赖 ──────→ 状态演化是顺序链，不可跳步
K3: 桥接输出状态依赖 ──→ 中间值不可静态预测
K4: 三份额缺一不可 ────→ 语义份额不可压缩 ✅

这四个定理合起来说：攻击者要想正确执行受保护程序，
必须模拟完整 VM 状态链（K2）、运行 G 混合器（K1）、
在运行时态下解码（K3）、使用全部三个份额（K4）。
```

---

## K1: G 混合器三轮是 (x,y,w) 上的置换

### 正式陈述

```
定理 K1 (gRounds_bijection):
  ∀ (x y w : Nat) (cfg : GMixerConfig),
    ∃ (inv : Nat × Nat × Nat → Nat × Nat × Nat),
      inv (gRounds_internal x y w cfg) = (x, y, w)
```

其中 `gRounds_internal` 是三轮 ARX+Q 复合（去掉最终 output mixing）。

### 证明策略

1. `one_round` 的 6 个子步骤每个都是可逆的（已证明：`step{a,b,c}_bij`, `qsub_{x,y}_bij`）
2. 单轮是 6 个可逆步骤的复合 → 单轮可逆（已证明：`one_round_inv_correct`）
3. 三轮是 3 个可逆轮的复合 → 三轮可逆
4. 三轮复合 → `gRounds_internal` 可逆

需要定义一个 `gRounds_internal` 函数（三轮复合但不包括 output mixing），然后证明它可逆。

### 状态

- 单轮可逆 ✅ 已证明
- 三轮可逆 ✅ 已证明（`gRounds_internal_inv_correct` + `one_round'_inv`）

### 依赖

- `one_round_inv_correct`（已证明） + `one_round'` 适配器

### 估计

- ~30 行新 Lean 代码 ✅ 已实现（新增 33 行）

---

## K2: H 链顺序依赖

### 正式陈述

```
定理 K2a (H_depends_on_Hprev):
  ∀ (h ra_val rb_val result edge mem call spawn ent_mix : Nat) (q : QAvalancheConfig),
    update_h h ra_val rb_val result edge mem call spawn ent_mix q =
    qAvalanche (h ^^^ digest(ra_val, rb_val) ^^^ rotl result 17 ^^^ edge ^^^ mem ^^^ call ^^^ spawn ^^^ ent_mix) q

  且 qAvalanche(·, q) 是 ℤ₂₆⁴ 上的置换（即双射）
```

```
定理 K2b (H_depends_on_operands):
  ∀ (h ra1 rb1 ra2 rb2 : Nat) (r : Nat) (e m c s em : Nat) (q : QAvalancheConfig),
    (ra1, rb1) ≠ (ra2, rb2) →
    update_h h ra1 rb1 r e m c s em q ≠ update_h h ra2 rb2 r e m c s em q
```

```
定理 K2c (sequential_chain):
  ∀ t, H_{t+1} ≠ H_t  （对大多数 t 成立——至少每步的 H 更新以高概率改变 H）
```

### 证明策略

K2a 的关键引理：`q_avalanche(x, q)` 在 x 上是双射（给定时 q 时）。
- `z1 = (x * mult) % 2^64`：mult 为奇数 → 乘奇数是 ℤ₂₆⁴ 上的双射
- `z2 = z1 ^^^ (shr z1 n)`：这是 Feistel 结构，在 ℤ₂₆⁴ 上双射（因为 `z → z ^ (z>>n)` 可逆：`z = z2 ^ (z>>n)`，可通过逐位恢复）
- `rotl64(z2, r)`：旋转是双射

### 状态

- `qAvalanche` 的 ℤ₂₆⁴ 双射未证明
- `digest_operands` 在 (ra, rb) 上的双射未证明
- "每步 H 变化"未证明

### 估计

- qAvalanche 双射：~60 行（需 ℤ₂₆⁴ 上的奇数乘、Feistel 可逆）
- H 链证明：~40 行

---

## K3: 桥接输出状态依赖

### 正式陈述

```
定理 K3 (bridge_varies_with_state):
  ∀ (c0 anchor c1_t c2 : Nat) (q : QAvalancheConfig),
    ∃ (σ₁ σ₂ DDM₁ DDM₂ : Nat),
      bridge_i41 c0 anchor c1_t c2 σ₁ DDM₁ q q ≠
      bridge_i41 c0 anchor c1_t c2 σ₂ DDM₂ q q
```

更强形式（对任意不同的 σ 成立）：

```
定理 K3_strong (bridge_different_for_different_sigma):
  ∀ (c0 anchor c1_t c2 σ σ' DDM : Nat) (q : QAvalancheConfig),
    qAvalanche σ q ≠ qAvalanche σ' q →
    bridge_i41 c0 anchor c1_t c2 σ DDM q q ≠
    bridge_i41 c0 anchor c1_t c2 σ' DDM q q
```

### 证明策略

桥接函数：`c0_eff = c0 ⊕ P(c1_t, σ) ⊕ P(anchor, 0) ⊕ P(c2, DDM) ⊕ P(c2, 0)`

其中 `P(val, state) = a·val + b mod 256`，`a = (qAvalanche(state,q)&0xFF)|1`，`b = (qAvalanche(state,q)>>8)&0xFF`。

唯一与 σ 相关的项是 `P(c1_t, σ)`。若 `qAvalanche(σ) ≠ qAvalanche(σ')`，则 P(c1_t, σ) 与 P(c1_t, σ') 在大多数情况下不同（但可能 `a≠a'` 或 `b≠b'`，若 `a≠a'` 则 `a·c1_t+b ≠ a'·c1_t+b` 当 `c1_t ≠ 0`，但 `c1_t = 0` 时仍可能 `b≠b'`）。

更强版本需要 `a≠a'` 或 `b≠b'`，这要求 `qAvalanche(σ)` 和 `qAvalanche(σ')` 的低 16 位不同。这不一定是真的。

实用证明：存在至少一对 σ,σ' 使桥接输出不同。（构造性：取 σ=0, σ'=1。若 qAvalanche(0) 和 qAvalanche(1) 的低 16 位相同，则尝试 σ=2，等等。最多 2^16 = 65536 种低 16 位值，所以最多尝试 65537 个 σ 值。可用 dec_trivial 枚举。）

### 状态

- 未证明

### 估计

- ~50 行（穷举或代数论证）

---

## K4: 三份额缺一不可

### 正式陈述

```
定理 K4a (share_anchor_required):
  ∀ (op anchor c2 : Nat) (q : QAvalancheConfig),
    let a_i := anchor  （假设 a_i ≠ 0）
    let c0 := encode_c0_i41 op anchor c2 q q
    let u := op
    in decode_i41 (bridge_i41 c0 0 c1_t c2 σ DDM q q) c1_t c2 σ DDM ≠ u
```

```
定理 K4b (share_c2_required):
  ∀ (op anchor c2 : Nat) (q : QAvalancheConfig),
    let c0 := encode_c0_i41 op anchor c2 q q
    decode_i41 (bridge_i41 c0 anchor c1_t 0 σ DDM q q) c1_t c2 σ DDM ≠ u
```

```
定理 K4c (share_c0_required):
  ∀ (op anchor c2 : Nat) (q : QAvalancheConfig),
    decode_i41 (bridge_i41 0 anchor c1_t c2 σ DDM q q) c1_t c2 σ DDM ≠ u
```

### 证明策略

**K4a**（anchor=0 而不是 a_i）：
展开 decode(bridge(encode(op, a_i, c2), 0, c1_t, c2, σ, DDM)) =
op ⊕ P(a_i, 0) ⊕ P(0, 0)

等于 op 当且仅当 P(a_i, 0) = P(0, 0)。
P(a_i, 0) = a₀·a_i + b₀，P(0, 0) = b₀，其中 a₀ = (qAvalanche(0,q)&0xFF)|1。
所以 P(a_i, 0) = P(0, 0) 当且仅当 a₀·a_i ≡ 0 (mod 256)。
由于 a₀ 是奇数，a₀·a_i ≡ 0  ⇒ a_i ≡ 0。
所以当 a_i ≠ 0 时 decode 结果 ≠ op。

**K4b**（c2=0 而不是 c2_from_edge(edge)）：
类似代数推导：当 c2 ≠ 0 时 decode 结果 ≠ op。

**K4c**（c0=0）：
直接在展开式中 c0=0 → decode 结果 ≠ op，因为 c0 在表达式中出现。

### 状态

- 全部已证明 ✅（`K4_ShareIndispensability.lean`: K4a/K4b/K4c + `anchor_zeroed_ne_u`）
- 代数消除已完成，纯 XOR 链重写

### 估计

- ~120 行（三个定理 + 两个辅助引理 + 一个推论）

---

## 优先级和执行计划

```
第一优先级（已完成）：
  K4: 三份额不可缺 ✅
  K1: G 混合器置换 ✅

第二优先级（当前）：
  K2: H 链顺序依赖
      理由：需要 qAvalanche 双射证明（基础），然后证明 H 依赖全部前序状态

第三优先级（补充论证）：
  K3: 桥接状态依赖
      理由：证明不依赖运行时态无法解码，但需要穷举或深入分析 q_avalanche
```

## 依赖图

```
K4（最低依赖）
  │
K2 ← qAvalanche 双射 + digest 双射
  │
K1 ← 组合三轮 one_round_inv
  │
K3 ← qAvalanche 双射（同 K2）
```

K4 无依赖，可以直接开始。
K2 和 K3 共享 qAvalanche 双射证明（优先做）。
K1 依赖最小但需要正确定义 gRounds_internal。
