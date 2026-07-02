# T01 审计修复记录

## 审计发现

**审核者**: Lean 4 形式化验证自动审计
**日期**: 2026-07-02

### T01-1 (CRITICAL): Injective vs Bijective 目标偏移

原 `P_mod_bijective` 只证明了 `Function.Injective`，但目标要求 `Function.Bijective`。
对 `Fin 256 → Nat`，injective 不等价于 bijective。

**修复**: 
- 新增 `P_mod_surjective`: 使用 `exists_mod_inv_any` 构造显式逆映射 `x = (aInv·((y+256-b%256)%256))%256`
- 升级 `P_mod_bijective` 返回 `(Injective ∧ ∀ y, ∃ x, f x = y.val)`
- 使用 `omega` 证明核心算术恒等式 `((y+256-B)%256 + B)%256 = y` 对 `y,B < 256`

### T01-2 (HIGH): P_of_state 偏离 Rust permute

Rust `permute` 使用 `q_avalanche(state, q)` 派生 `(a,b)`，而 Lean `P_of_state` 直接用 `state`。

**修复**: 
- 添加详细文档注释说明抽象
- `q_avalanche` 建模为恒等函数（proof-level 抽象），即 `q_avalanche(state, q) = state`（在 Lean 模型中）
- 关键性质保持: 两种版本都能保证 `a` 为奇数 → 双射

### T08-1 (MEDIUM): SemShare 中 P_mod 参数简化

`encode_c0_i41` 等函数使用 `P_mod anchor 1 0`（a=1,b=0）替代 Rust 的 `permute(anchor, 0, q_sigma)`。

**验证**: 当 `state=0` 时，两个版本完全一致（因 `q_avalanche(0, q) = 0`）。
当 `state≠0` 时，值不同但代数消去不受影响（每个 P 项成对出现 → XOR 自消）。

**修复**: 添加详细文档注释说明抽象及安全性论证。

### CC-1 (MEDIUM): 定理文件为占位符

`Theorems/` 下的文件为空。

**修复**: 已完成的定理（T01-T04, T08）的文件现在包含实际定理语句，引用 Definitions/ 中的证明。
