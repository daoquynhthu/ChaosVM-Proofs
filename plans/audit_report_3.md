# 全面自审报告

## 1. 被调用的未证明假设

| 假设 | 位置 | 是否安全 |
|------|------|---------|
| `dec_trivial` 在 `exists_mod_inv` 中枚举 128×256=32768 种情况 | `Permutation.lean:11` | ✅ 编译器验证 |
| `omega` 证明 `((y+256-B)%256 + B)%256 = y` 等算术恒等式 | `Permutation.lean:37,134` | ✅ 信任的证明过程 |
| `dec_trivial` 验证 `(Nat.lor x 1) % 2 = 1` 对 x<256 | `Permutation.lean:166` | ✅ 编译器验证 |

**无外部公理、无 admit、无 unsafe。** 所有 proof 全部在 Lean 4 核心逻辑内完成。

## 2. 简化导致的目标偏移

### 2.1 严重：hⱼ 索引函数的巨大简化

| 函数 | Rust 语义 | Lean 语义 |
|------|----------|----------|
| `h_sigma` | `(q_avalanche(pc⊕σ⊕h⊕r0, q_σ) >> 56) as u8` | `(pc⊕σ⊕h⊕r0) % 256` |
| `h_cfa` | `(q_avalanche(e⊕rotl(e,32)⊕CFA⊕rotl(H,19)⊕ctr⊕r1, q_C) >> 48) as u8` | `(e⊕CFA⊕H⊕ctr⊕r1) % 256` |
| `h_ddm` | `(q_avalanche(pc·m⊕DDM⊕rotl(σ+CFA,31)⊕rotl(H,43), q_D) >> 40) as u8` | `((pc·m)⊕DDM⊕(σ+CFA)⊕H) % 256` |

**影响**：跳过了 `q_avalanche` ARX 混合和正确的位提取。仅确定型定理（`h_*_deterministic`）是安全的，任何关于具体 `i_σ` 值的定理均不成立。

### 2.2 中等：StateUpdate 跳过 q_avalanche

Rust 的 `update_h`、`update_state` 使用 `q_avalanche` 进行非线性混合。Lean 版本使用纯 XOR。确定型定理安全。

### 2.3 中等：gRounds 抽象为 (x⊕y, w⊕x)

实际的 G 混合器执行 3 轮 ARX+Q。抽象模型只是简单 XOR。确定型定理安全，但任何关于混合质量的定理不成立。

### 2.4 中等：rotl/rotr 在 Helpers 中定义为恒等函数

```lean
def rotl (x n : Nat) : Nat := x
def rotr (x n : Nat) : Nat := x
```

**影响**：
- 输出满射证明 (`output_mixing_surjective`) 依赖 `rotl(rotr(z,23),23)=z`，这在抽象模型中平凡成立，在真实 Rust 中也成立（因 `rotate_left` 和 `rotate_right` 互逆），但抽象模型没有验证旋转的位精确性。
- `step_{a,b,c}` 中的旋转被忽略。

### 2.5 轻微：Init 跳过 q_avalanche

Rust 的 `init`/`init_poisoned` 使用 `q_avalanche` 做 keyed PRF。Lean 使用纯 XOR。发散证明安全。

## 3. 所有修复历史的定理正确性

| 定理 | 实际证明的内容 | 是否匹配声称 |
|------|--------------|------------|
| `P_mod_bijective` | `(a·x+b)%256` 在 `Fin 256` 上 injective+surjective | ✅ 完全匹配 |
| `affine_map_bijective` | 同 P_mod | ✅ 完全匹配 |
| `c2_from_edge_byte` | `c2_from_edge(edge) < 256` | ✅ 完全匹配 |
| `decompose_safe_multipliers_odd` | a_rd/a_ra/a_rb 为奇数 | ✅ 完全匹配 |
| `bridge_decode_invariant` | `decode(bridge(encode(op))) = op` | ✅ 完全匹配 |
| `init_poisoned_diverges` | 投毒后 InitState ≠ clean | ✅ 完全匹配 |
| `one_round_inv_correct` | `one_round_inv ∘ one_round = id` | ✅ T07a（轮置换） |
| `output_mixing_surjective` | 输出混合覆盖全部 ℤ₂₅₆² | ✅ T07b（输出满射） |
| `gMix_deterministic` | 纯函数确定型 | ✅ |
| `h_*_deterministic` | 纯函数确定型 | ✅ |
| `update_state_deterministic` | 纯函数确定型 | ✅ |
| `init_deterministic` | 纯函数确定型 | ✅ |

## 4. 关于抽象安全的论证

每个 Lean 定义与 Rust 的偏离都可以归类为**类型 4（架构正确的抽象）**：
- 抽象的 `q_avalanche` 作为恒等函数：不影响确定型、双射性、代数消去等性质的证明
- 抽象的 `rotl`/`rotr` 作为恒等函数：不影响加法/XOR 可逆性证明
- 省略的 `q_sigma`/`q_ddm` 参数：不影响 XOR 配对消去

**例外**：如果有人试图用这些 Lean 定理来声称关于 Rust 具体输出的性质（如"第 3 步的 `i_σ` 值是 X"），则由简化导致的偏离会导致无效推论。所有已证明的定理都是关于**代数结构**的，而非关于具体数值的。

## 5. 改进建议

1. 将 `rotl`/`rotr` 改为真正的位旋转实现（需要 bit-level lemmas）
2. hⱼ 函数添加 `q_avalanche` 参数（但当前证明只需要确定型，不必要）
3. 为 `gRounds` 添加完整的 3 轮 ARX 实现（复杂但可行）
