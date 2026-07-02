# 第二次审计报告：定理 T01 & T08 复核

## 复核方法

逐行对比 Rust 源码 (`sem_share.rs`, `reg_map.rs`) 与 Lean 形式化模型，按四种分类标识每个偏差。

**分类定义**：
1. **Rust bug** — 实现本身有数学错误（攻击面）
2. **证明简化错误** — Lean 模型过于简化，导致证明了与 Rust 不同的性质
3. **适配错误** — 正确思路在形式化过程中被改错
4. **架构正确的抽象** ✅ — 证明与代码不一致，但符合架构设计哲学

---

## T01: P_mod 双射性

### 结论：分类 4 ✅

**Rust `permute`** (`sem_share.rs:56-61`):
```rust
fn permute(val: u8, state: u64, q: &QAvalanche) -> u8 {
    let mix = q_avalanche(state, q);
    let a = (mix as u8) | 1;     // always odd
    let b = (mix >> 8) as u8;
    a.wrapping_mul(val).wrapping_add(b)
}
```

**Lean `P_mod_bijective`** (`Permutation.lean:81-89`):
```lean
theorem P_mod_bijective (a b : Nat) (ha_odd : a % 2 = 1) :
    Function.Injective (λ (x : Fin 256) => ((a * x.val + b) % 256 : Nat)) ∧
    (∀ (y : Fin 256), ∃ (x : Fin 256), ((a * x.val + b) % 256 : Nat) = y.val) := ...
```

**性质对照**：
| 维度 | Rust `permute` | Lean `P_mod` | 一致？ |
|------|----------------|-------------|--------|
| 乘法 | `a.wrapping_mul(val)` (u8, mod 256) | `(a * x) % 256` (Nat) | ✅ 等价 |
| 加法 | `.wrapping_add(b)` (u8, mod 256) | `(... + b) % 256` | ✅ 等价 |
| a 来源 | `(q_avalanche(state,q) as u8) \| 1` | 直接传入 | ⚠️ 抽象 |
| b 来源 | `(q_avalanche(state,q) >> 8) as u8` | 直接传入 | ⚠️ 抽象 |

**判断依据**：`P_mod_bijective` 的证明不依赖 `a,b` 的来源，只要求 `a` 为奇数。Rust 的 `a = (mix as u8) | 1` 保证奇数。**Lean 证明了更强的性质**（对所有奇数 a 和任意 b 成立），因此 Rust 的 `permute` 自动继承此性质。

**Rust 测试验证**：`reg_map.rs:94-104` 的 `affine_map_is_bijection` 对所有奇数 a 验证了双射性。

**是否类型 3（正确思路改错）**：否。Lean 的 `P_mod` 核心算术 `(a·x + b) % 256` 与 Rust 的 `a.wrapping_mul(x).wrapping_add(b)` 在 u8/Nat 语义下一致。

---

## T01 子项: P_of_state 与 permute 的偏差

### 结论：分类 4 ✅（但需关注）

**Rust**:
```rust
fn permute(val: u8, state: u64, q: &QAvalanche) -> u8 {
    let mix = q_avalanche(state, q);  // ← 非线性 ARX
    let a = (mix as u8) | 1;
    let b = (mix >> 8) as u8;
    a.wrapping_mul(val).wrapping_add(b)
}
```

**Lean**:
```lean
def P_of_state (x state : Nat) : Nat :=
  let a := Nat.lor (state % 256) 1
  let b := (state / 256) % 256
  P_mod x a b
```

**关键差异**：
| 步骤 | Rust | Lean |
|------|------|-------|
| mix 计算 | `q_avalanche(state, q)` — 3 轮 ARX | `state` 直接使用 |
| a 提取 | `(mix as u8) \| 1` | `(state % 256) \| 1` |
| b 提取 | `(mix >> 8) as u8` | `(state / 256) % 256` |

**安全论证**：Rust 的 `mix = q_avalanche(state, q)` 是比 `state` 更"熵高"的输入。由于 `P_mod` 的证明只要求 `a` 为奇数，而两种方式都保证 `a` 为奇数，**双射性结论在 Rust 中成立**。

**是否类型 2（证明简化错误）**：否。证明的是 `P_mod` 的高层性质，不依赖于 `a,b` 的具体推导方式。如果有人从 Lean 证明直接断言 `P_of_state` 的精确输出值匹配 Rust 的 `permute`，那将是错误的——但所有定理仅关于代数结构，不涉及数值相等。

---

## T08: Bridge+Decode Invariant

### 结论：分类 4 ✅

**Rust 管线**:
```
encode: c0 = u ⊕ P(a,0,qσ) ⊕ P(c2,0,qδ)
bridge: c0_eff = c0 ⊕ P(c1,σ,qσ) ⊕ P(a,0,qσ) ⊕ P(c2,δ,qδ) ⊕ P(c2,0,qδ)
decode: v = c0_eff ⊕ P(c1,σ,qσ) ⊕ P(c2,δ,qδ)
```

**代数消去验证（逐项检查 Rust 代码）**：
```
v = u ⊕ P(a,0,qσ) ⊕ P(c2,0,qδ)                    [encode]
      ⊕ P(c1,σ,qσ) ⊕ P(a,0,qσ) ⊕ P(c2,δ,qδ) ⊕ P(c2,0,qδ) [bridge]
      ⊕ P(c1,σ,qσ) ⊕ P(c2,δ,qδ)                           [decode]
```

配对检查（每个 `permute` 调用出现两次，参数完全相同）：
| 项 | 出现于 | 配对 | 状态 |
|----|--------|------|------|
| `P(a,0,qσ)` | encode + bridge | `P(a,0,qσ) ⊕ P(a,0,qσ)` | ✅ 自消 |
| `P(c2,0,qδ)` | encode + bridge | `P(c2,0,qδ) ⊕ P(c2,0,qδ)` | ✅ 自消 |
| `P(c1,σ,qσ)` | bridge + decode | `P(c1,σ,qσ) ⊕ P(c1,σ,qσ)` | ✅ 自消 |
| `P(c2,δ,qδ)` | bridge + decode | `P(c2,δ,qδ) ⊕ P(c2,δ,qδ)` | ✅ 自消 |

**Rust 实现正确性**：管线是**数学正确的**。所有 4 对 `permute` 以完全相同参数出现，XOR 自消 → 结果为 `u`。不存在类型 1 漏洞。

**Lean 模型偏差**：
| 调用 | Rust | Lean | 一致？ |
|------|------|------|--------|
| `P(anchor,0,qσ)` | `permute(anchor,0,qσ)=anchor` | `P_mod anchor 1 0 = anchor` | ✅ 数值一致 |
| `P(c2,0,qδ)` | `permute(c2,0,qδ)=c2` | `P_mod c2 1 0 = c2` | ✅ 数值一致 |
| `P(c1,σ,qσ)` | `a·c1+b` (a,b 来自 q_avalanche) | `(c1+σ)%256` | ⚠️ 值不同 |
| `P(c2,δ,qδ)` | `a·c2+b` (a,b 来自 q_avalanche) | `(c2+δ)%256` | ⚠️ 值不同 |

**是否类型 2（简化错误）**：否。消去证明仅依赖于**配对结构**，不依赖具体值。Rust 中每个 `permute` 确定性调用出现两次 → 异或为 0。Lean 中每个 `P_mod` 调用出现两次 → 异或为 0。

**是否类型 3（适配错误）**：否。Lean 代码缺失 `q_sigma`/`q_ddm` 参数是故意的抽象（documented in abstraction note），不影响定理结论。

---

## 跨定理审核

### q_avalanche(0, q) = 0 验证

这是 `state=0` 时 Lean 与 Rust 数值一致的关键。

```rust
q_avalanche(0, p):
  0.wrapping_mul(p.mult) = 0
  0 ^= 0 >> p.xor_shift = 0
  0.rotate_left(p.rot) = 0
```

对于任意 QAvalanche 参数，`q_avalanche(0, q) = 0`。✅

因此 `permute(anchor, 0, q_sigma) = (0|1)·anchor + 0 = anchor`。与 `P_mod anchor 1 0` 完全一致。✅

### P_mod_bijective 的 `Injective` vs `Bijective`

首次审计发现只证明了 `Injective`，缺少 `Surjective`。已修复：新增 `P_mod_surjective` 使用显式逆映射 `x = aInv·((y+256-b%256)%256)%256`。

**修复验证**：
```
P_mod x a b = (a * (aInv * ((y+256-b%256)%256)) + b) % 256
            = ((a*aInv) * ((y+256-b%256)%256) + b) % 256
            = (1 * ((y+256-b%256)%256) + b) % 256    [by h_inv]
            = ((y+256-b%256)%256 + b%256) % 256
            = y                                         [by omega]
```

证明使用 `Init.Omega` 处理算术恒等式 `∀ y,B<256: ((y+256-B)%256 + B)%256 = y`。✅

---

## Rust 代码数学正确性检查

检查了 `sem_share.rs:56-134` 和 `reg_map.rs:26-28`，未发现数学错误。

具体检查点：
- `permute` 中 `a = (mix as u8) | 1` 保证奇数 ✅（`| 1` 设置最低位）
- `affine_map` 在 u8 域上是双射 ✅（奇数乘数 + 模 256 加法）
- `encode/bridge/decode` 管线代数正确 ✅（4 对异或自消）
- `q_avalanche(0, q) = 0` 对任意 q 成立 ✅

---

## 最终结论

| 项目 | 类型 | 说明 |
|------|------|------|
| T01 Rust `permute` | 无类型 1 | 实现正确，双射性成立 |
| T01 Lean `P_mod_bijective` | **类型 4** ✅ | 抽象了 q_avalanche，但核心性质（奇数 a → 双射）正确覆盖 Rust |
| T01 Lean `P_of_state` | **类型 4** ✅ | 偏 `state` 代替 `q_avalanche(state,q)`，但不影响定理结论 |
| T08 Rust 管线 | 无类型 1 | 代数消去正确，不变性成立 |
| T08 Lean `bridge_decode_invariant` | **类型 4** ✅ | 缺失 q 参数但配对结构保留，消去证明正确 |
| T08 `P_mod c1_t 1 σ` vs `permute(c1_t,σ,qσ)` | **类型 4** ✅ | 值不同但消去不依赖具体值 |
| T08 文档注释 | 已修复 | 添加 abstraction note，解释所有偏差 |

**无类型 2（证明简化错误）**：所有简化保留了证明所需的代数结构。
**无类型 3（适配错误）**：证明逻辑正确，没有为了适配代码而扭曲证明。
**可操作的下一步**：T13 (`init_poisoned_diverges`) 和 T07 (G 混合器双射) 仍待完成。
