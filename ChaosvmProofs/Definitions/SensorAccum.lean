/-
  SensorAccum.lean — 传感器积累正确性模型
-/

namespace ChaosvmProofs.Definitions.SensorAccum

structure SensorResult where
  s : Nat
  c : Nat
  d : Nat
  s_bound : s ≤ 3
  c_bound : c ≤ 3
  d_bound : d ≤ 3

structure WeightedSensor where
  result : SensorResult
  weight : Nat
  weight_pos : weight ≥ 1

structure PoisonAccumulator where
  p_sigma : Nat
  p_cfa : Nat
  p_ddm : Nat
  sigma_bound : p_sigma ≤ 255
  cfa_bound : p_cfa ≤ 255
  ddm_bound : p_ddm ≤ 255

def accum_channel (p : Nat) (x weight : Nat) : Nat :=
  if p + weight * x ≤ 255 then p + weight * x else 255

-- ============================================================================
-- 核心性质
-- ============================================================================

theorem accum_channel_bound (p x weight : Nat) :
    accum_channel p x weight ≤ 255 := by
  unfold accum_channel; split <;> omega

theorem accum_channel_mono_input (p x₁ x₂ w : Nat) (h : x₁ ≤ x₂) :
    accum_channel p x₁ w ≤ accum_channel p x₂ w := by
  unfold accum_channel
  have hmul : w * x₁ ≤ w * x₂ := Nat.mul_le_mul_left w h
  split <;> split
  · exact Nat.add_le_add_left hmul p
  · assumption
  · omega
  · exact Nat.le_refl 255

theorem accum_channel_mono_acc (p₁ p₂ x w : Nat) (h : p₁ ≤ p₂) :
    accum_channel p₁ x w ≤ accum_channel p₂ x w := by
  unfold accum_channel; split <;> split
  · exact Nat.add_le_add_right h (w * x)
  · assumption
  · omega
  · exact Nat.le_refl 255

theorem accum_channel_ge_acc (p x w : Nat) (hp : p ≤ 255) :
    accum_channel p x w ≥ p := by
  unfold accum_channel; split
  · exact Nat.le_add_right _ _
  · exact hp

theorem accum_channel_lower (p x w : Nat) (_hx : x > 0) (hw : w ≥ 1)
    (hle : p + w * x ≤ 255) :
    accum_channel p x w ≥ p + x := by
  unfold accum_channel
  have hxle : 1 * x ≤ w * x := Nat.mul_le_mul_right x hw
  simp only [Nat.one_mul] at hxle
  split <;> omega

-- ============================================================================
-- 完整累加器
-- ============================================================================

def accumulate (acc : PoisonAccumulator) (ws : WeightedSensor) : PoisonAccumulator :=
  ⟨ accum_channel acc.p_sigma ws.result.s ws.weight,
    accum_channel acc.p_cfa ws.result.c ws.weight,
    accum_channel acc.p_ddm ws.result.d ws.weight,
    accum_channel_bound _ _ _,
    accum_channel_bound _ _ _,
    accum_channel_bound _ _ _ ⟩

theorem accumulate_bound (acc : PoisonAccumulator) (ws : WeightedSensor) :
    (accumulate acc ws).p_sigma ≤ 255 ∧
    (accumulate acc ws).p_cfa ≤ 255 ∧
    (accumulate acc ws).p_ddm ≤ 255 :=
  ⟨accum_channel_bound _ _ _, accum_channel_bound _ _ _, accum_channel_bound _ _ _⟩

theorem accumulate_mono_result
    (acc : PoisonAccumulator) (ws₁ ws₂ : WeightedSensor)
    (hs : ws₁.result.s ≤ ws₂.result.s)
    (hc : ws₁.result.c ≤ ws₂.result.c)
    (hd : ws₁.result.d ≤ ws₂.result.d)
    (hw : ws₁.weight = ws₂.weight) :
    (accumulate acc ws₁).p_sigma ≤ (accumulate acc ws₂).p_sigma ∧
    (accumulate acc ws₁).p_cfa ≤ (accumulate acc ws₂).p_cfa ∧
    (accumulate acc ws₁).p_ddm ≤ (accumulate acc ws₂).p_ddm := by
  refine ⟨?_, ?_, ?_⟩
  · show accum_channel acc.p_sigma ws₁.result.s ws₁.weight ≤ accum_channel acc.p_sigma ws₂.result.s ws₂.weight
    rw [hw]; exact accum_channel_mono_input _ _ _ _ hs
  · show accum_channel acc.p_cfa ws₁.result.c ws₁.weight ≤ accum_channel acc.p_cfa ws₂.result.c ws₂.weight
    rw [hw]; exact accum_channel_mono_input _ _ _ _ hc
  · show accum_channel acc.p_ddm ws₁.result.d ws₁.weight ≤ accum_channel acc.p_ddm ws₂.result.d ws₂.weight
    rw [hw]; exact accum_channel_mono_input _ _ _ _ hd

-- ============================================================================
-- 充分性
-- ============================================================================

theorem accumulate_increases_on_detection
    (acc : PoisonAccumulator) (ws : WeightedSensor)
    (h_s : ws.result.s > 0) (h_w : ws.weight ≥ 1)
    (h_sat : acc.p_sigma + ws.weight * ws.result.s < 255) :
    (accumulate acc ws).p_sigma > acc.p_sigma := by
  show accum_channel acc.p_sigma ws.result.s ws.weight > acc.p_sigma
  unfold accum_channel; split
  · exact Nat.lt_add_of_pos_right (Nat.mul_pos h_w h_s)
  · rename_i h; exact absurd h_sat (by omega)

def zeroAccum : PoisonAccumulator :=
  ⟨0, 0, 0, by omega, by omega, by omega⟩

theorem accumulate_nonzero_from_zero
    (ws : WeightedSensor)
    (h_s : ws.result.s > 0) (h_w : ws.weight ≥ 1)
    (h_bound : ws.weight * ws.result.s ≤ 255) :
    (accumulate zeroAccum ws).p_sigma > 0 := by
  show accum_channel 0 ws.result.s ws.weight > 0
  unfold accum_channel; split
  · simp only [Nat.zero_add]; exact Nat.mul_pos h_w h_s
  · rename_i h; exact absurd h (by omega)

-- ============================================================================
-- 批量累加
-- ============================================================================

def accumulate_all (sensors : List WeightedSensor) : PoisonAccumulator :=
  sensors.foldl accumulate zeroAccum

theorem accumulate_all_bound (sensors : List WeightedSensor) :
    (accumulate_all sensors).p_sigma ≤ 255 ∧
    (accumulate_all sensors).p_cfa ≤ 255 ∧
    (accumulate_all sensors).p_ddm ≤ 255 := by
  unfold accumulate_all
  suffices h : ∀ acc, acc.p_sigma ≤ 255 → acc.p_cfa ≤ 255 → acc.p_ddm ≤ 255 →
    (sensors.foldl accumulate acc).p_sigma ≤ 255 ∧
    (sensors.foldl accumulate acc).p_cfa ≤ 255 ∧
    (sensors.foldl accumulate acc).p_ddm ≤ 255 from
    h zeroAccum zeroAccum.sigma_bound zeroAccum.cfa_bound zeroAccum.ddm_bound
  intro acc hs hc hd
  induction sensors generalizing acc with
  | nil => exact ⟨hs, hc, hd⟩
  | cons ws rest ih =>
    simp only [List.foldl]
    exact ih _ (accum_channel_bound _ _ _) (accum_channel_bound _ _ _) (accum_channel_bound _ _ _)

-- ============================================================================
-- 传感器范围约束
-- ============================================================================

def valid_sensor_result (r : SensorResult) : Prop :=
  r.s ≤ 3 ∧ r.c ≤ 3 ∧ r.d ≤ 3

theorem max_contribution (ws : WeightedSensor) (h : valid_sensor_result ws.result) :
    ws.weight * ws.result.s ≤ ws.weight * 3 :=
  Nat.mul_le_mul_left ws.weight h.1

end ChaosvmProofs.Definitions.SensorAccum
