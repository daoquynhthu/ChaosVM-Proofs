# ChaosVM Proofs — 形式化证明进度

> Lean 4.30，仅依赖 `Init.Omega`，无 Mathlib。

## 已完成定理

| 定理 | 文件 | 状态 |
|------|------|------|
| `no_inj_gt_range` | `K3_BridgeStateDependency.lean` | ✅ |
| `exists_sigma_permute_diff` | `K3_BridgeStateDependency.lean` | ✅ |
| `K3_bridge_varies_with_state` | `K3_BridgeStateDependency.lean` | ✅ |

## 构建状态

`lake build ChaosvmProofs` — 37 jobs, 0 errors, 0 warnings ✅

## 关键修复记录

### 2026-07-03 — K3 三定理全部完成

**解决的问题**：
1. **栈溢出** — `permute_eq_mod_form` 展开定理移至 `Permutation.lean`
2. **`xor_quad_cancel`** — 新增 `theorem` 级（`lemma` 导致 parse error）
3. **`h_lo_eq_coeff`** — 使用 `let` 定义时不能用 `unfold`，改用 `rw [h_lor]` 直接引用 `lo` 而非展开
4. **`hperm0` calc 冗余** — 删除多余 `calc` 行，`simp` 已直接证明
5. **linter 警告** — 移除未使用的 `simp` 参数（`Nat.mul_mod`、`Nat.mod_mod`），用 `rw` 替代 `simpa`/`simp`
