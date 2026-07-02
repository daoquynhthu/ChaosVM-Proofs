# T01: P_mod 双射性 — 证明计划

## 问题

证明 `P_mod x a b = (a·x + b) % 256` 在 `x ∈ {0,...,255}` 上双射，前提是 `a` 为奇数。

## 策略总览

```
不依赖数论（扩展欧几里得、互质），使用 brute-force 有限域验证。
域大小为 256=2⁸，dec_trivial 可处理。
```

## 子任务分解

### 1.1 定义 Fin 256 上的有界函数

将 P_mod 限制到 `Fin 256 → Fin 256`：

```lean
def P_mod_a0_fin (a : ℕ) (x : Fin 256) : Fin 256 := ⟨(a * x.val) % 256, ...⟩
def P_mod_fin (a b : ℕ) (x : Fin 256) : Fin 256 := ⟨(a * x.val + b) % 256, ...⟩
```

### 1.2 证明 a=0 偏移时双射 (dec_trivial)

对每个奇数 `a < 256`，验证 `P_mod_a0_fin a` 是 `Fin 256` 上的双射。

- 128 个 a 值，每个需 256² = 65536 次 injectivity 检查
- 总检查量: 128 × 65536 ≈ 8.4M — dec_trivial 可处理
- 同时验证 surjectivity: 256 × 256 = 65536 额外检查（总约 16.8M）

### 1.3 常数偏移保持双射性

证明若 `f : Fin 256 → Fin 256` 是双射，则 `λ x → (f x + b) % 256` 也是双射。

- 这等价于证明 `Fin 256` 上的加法（模 256）是置换
- 对每个 `b < 256`，映射 `y ↦ (y + b) % 256` 是双射（dec_trivial 验证：256 个 b）

### 1.4 从 a<256 扩展到任意 ℕ

利用模简化：`(a * x) % 256 = ((a % 256) * x) % 256`

对任意 `a : ℕ`，有 `a' = a % 256 < 256`，且：
- 若 `a` 为奇数，则 `a'` 也为奇数（因为 256 是偶数）
- `P_mod_a0_fin a = P_mod_a0_fin a'`（由模算术相等）

### 1.5 组合为最终定理

```lean
theorem P_mod_bijective (a b : ℕ) (ha : a % 2 = 1) :
    Function.Bijective (λ (x : Fin 256) => ((a * x.val + b) % 256 : ℕ)) := ...
```

### 1.6 应用到 affine_map (T02)

`affine_map r a b = (a·r + b) % 256`，与 P_mod 完全相同。

因此 T02 即 T01 的重述。

## 验证方法

每个子任务完成后运行 `lake build` 确认编译通过。
所有 dec_trivial 验证在编译期完成（约 100ms 额外时间）。
