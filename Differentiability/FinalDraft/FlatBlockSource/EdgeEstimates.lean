/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatTop.HalfLineSpeed
public import Differentiability.Probability.HalfLineEdge
import Differentiability.Probability.HalfLineEdgeDeviation
import Differentiability.Probability.AugmentedMeasurability
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Tactic

/-! The two half-line estimates used to confine the crossing in Durrett (1984),
p. 1025. The spatial coordinate in that proof is the difference of the two
coordinates, so its speed is twice the first-coordinate speed minus one. -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators

namespace LPPDifferentiability.FinalDraft.FlatBlockSource

/-- The right edge in the rotated space coordinate of Durrett's model. -/
noncomputable def rotatedEdge (ω : Environment) (n : ℕ) : ℝ :=
  2 * (halfLineEdge ω n : ℝ) - (n : ℝ)

/-- With vertical scale `L = 20N`, this is the rounded spatial unit
`α L / 20` in Durrett's block. -/
noncomputable def roundedWidth (α : ℝ) (N : ℕ) : ℤ := ⌊α * (N : ℝ)⌋

/-- The deviation event in (7.2) at any slope above the actual edge speed,
using the existing exponential upper-deviation theorem on the same site law. -/
theorem exponential_rotatedEdge_upper (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : 0 < ν {1}) {β b : ℝ} (hb : 2 * β - 1 < b)
    (hβ : IsGLB (Set.range fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)) β) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ n : ℕ,
      (environmentLaw ν).real {ω | b * (n : ℝ) ≤ rotatedEdge ω n} ≤
        A * Real.exp (-(B * n)) := by
  let c := (b + 1) / 2
  have hc : β < c := by dsimp [c]; linarith
  obtain ⟨j, hj⟩ : ∃ j : ℕ,
      (∫ ω, (halfLineEdge ω (j + 1) : ℝ) ∂environmentLaw ν) / ((j : ℝ) + 1) < c := by
    by_contra! h
    exact hc.not_ge (hβ.2 (by rintro _ ⟨j, rfl⟩; exact h j))
  have hmean : (∫ ω, (halfLineEdge ω (j + 1) : ℝ) ∂environmentLaw ν) <
      c * ((j + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_succ]
    exact (div_lt_iff₀ (by positivity : 0 < (j : ℝ) + 1)).mp hj
  obtain ⟨A, B, hA, hB, htail⟩ :=
    halfLineEdge_upper_deviation ν hν c (j + 1) (Nat.succ_pos j) hmean
  refine ⟨A, B, hA, hB, fun n => ?_⟩
  have hset : {ω | b * (n : ℝ) ≤ rotatedEdge ω n} =
      {ω | c * (n : ℝ) ≤ (halfLineEdge ω n : ℝ)} := by
    ext ω
    simp only [mem_ofPred_eq, c, rotatedEdge, add_mul, div_mul_eq_mul_div, one_mul]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact htail n

/-- The centered edge is measurable at each time. -/
theorem measurable_rotatedEdge (n : ℕ) : Measurable (fun ω => rotatedEdge ω n) := by
  have hm : Measurable (fun ω => halfLineEdge ω n) :=
    (measurable_openEdge_levelsAtMost antidiagHalfLine 0 antidiagHalfLine_subset_levelSet n).mono
      (levelsAtMost_le _) le_rfl
  have hm' : Measurable (fun ω => (halfLineEdge ω n : ℝ)) :=
    (Measurable.of_discrete (f := fun z : ℤ => (z : ℝ))).comp hm
  exact (measurable_const.mul hm').sub measurable_const

/-- The failure of the all-time edge bound in the finite box is measurable. -/
theorem measurableSet_box_failure (α : ℝ) (N : ℕ) :
    MeasurableSet {ω : Environment | ¬ ∀ n ≤ 22 * N,
        |rotatedEdge ω n - α * (n : ℝ)| ≤ (roundedWidth α N : ℝ) / 5} := by
  have hm (n : ℕ) : Measurable (fun ω : Environment =>
      |rotatedEdge ω n - α * (n : ℝ)|) :=
    (continuous_abs.measurable : Measurable (fun r : ℝ => |r|)).comp
      ((measurable_rotatedEdge n).sub_const (α * (n : ℝ)))
  have heq : {ω : Environment | ¬ ∀ n ≤ 22 * N,
      |rotatedEdge ω n - α * (n : ℝ)| ≤ (roundedWidth α N : ℝ) / 5} =
      (⋂ n : {n : ℕ // n ≤ 22 * N},
        {ω | |rotatedEdge ω n.val - α * (n.val : ℝ)| ≤
          (roundedWidth α N : ℝ) / 5})ᶜ := by
    ext ω
    simp
  rw [heq]
  exact (MeasurableSet.iInter fun n : {n : ℕ // n ≤ 22 * N} =>
    measurableSet_le (hm n.val) measurable_const).compl

private theorem eventually_uniform_of_speed {ω : Environment} {β α : ℝ}
    (hαeq : α = 2 * β - 1) (hα : 0 < α)
    (hω : Tendsto (fun n : ℕ => (halfLineEdge ω n : ℝ) / (n : ℝ)) atTop (𝓝 β)) :
    ∀ᶠ N : ℕ in atTop, ∀ n ≤ 22 * N,
      |rotatedEdge ω n - α * (n : ℝ)| ≤ (roundedWidth α N : ℝ) / 5 := by
  have hnear := (Metric.tendsto_nhds.mp hω) (α / 1000) (by positivity)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hnear.and (eventually_ge_atTop 1))
  let err (n : ℕ) : ℝ := |rotatedEdge ω n - α * (n : ℝ)|
  let B : ℝ := ∑ n ∈ Finset.range K, err n
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have herr (n : ℕ) : err n ≤ α * (n : ℝ) / 500 + B := by
    by_cases hn : K ≤ n
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast (hK n hn).2
      have hd : |(halfLineEdge ω n : ℝ) / (n : ℝ) - β| < α / 1000 := by
        simpa only [Real.dist_eq] using (hK n hn).1
      have heq : rotatedEdge ω n - α * (n : ℝ) =
          ((halfLineEdge ω n : ℝ) / (n : ℝ) - β) * (2 * (n : ℝ)) := by
        rw [hαeq]
        unfold rotatedEdge
        field_simp [hnpos.ne']
        ring
      have hmul := mul_le_mul_of_nonneg_right hd.le (show 0 ≤ 2 * (n : ℝ) by positivity)
      dsimp [err]
      rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (n : ℝ))]
      linarith
    · have hterm : err n ≤ B :=
        Finset.single_le_sum (f := err) (fun i _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
      linarith [mul_nonneg hα.le (show (0 : ℝ) ≤ n by positivity)]
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((10 * B + 10) / α)
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hlarge : 10 * B + 10 < α * (N : ℝ) := by
    have hc : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
    simpa only [mul_comm (N : ℝ) α] using (div_lt_iff₀ hα).mp (hN₀.trans_le hc)
  have hfloor := Int.lt_floor_add_one (α * (N : ℝ))
  intro n hn
  have hcast : (n : ℝ) ≤ 22 * (N : ℝ) := by exact_mod_cast hn
  have hs := mul_le_mul_of_nonneg_left hcast hα.le
  have he := herr n
  dsimp [err] at he
  change _ ≤ ((⌊α * (N : ℝ)⌋ : ℤ) : ℝ) / 5
  linarith

/-- Convergence of the actual half-line edge gives a uniform all-time
error bound up to level `22N`, with high probability. -/
theorem rotatedEdge_uniform_failure_tendsto (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {β : ℝ} (hβ : 1 / 2 < β)
    (hlim : ∀ᵐ ω ∂environmentLaw ν,
      Tendsto (fun n : ℕ => (halfLineEdge ω n : ℝ) / (n : ℝ)) atTop (𝓝 β)) :
    Tendsto (fun N : ℕ => (environmentLaw ν).real
      {ω | ¬ ∀ n ≤ 22 * N,
        |rotatedEdge ω n - (2 * β - 1) * (n : ℝ)| ≤
          (roundedWidth (2 * β - 1) N : ℝ) / 5}) atTop (𝓝 0) := by
  let α := 2 * β - 1
  have hα : 0 < α := by dsimp [α]; linarith
  let F (N : ℕ) : Set Environment := {ω | ¬ ∀ n ≤ 22 * N,
    |rotatedEdge ω n - α * (n : ℝ)| ≤ (roundedWidth α N : ℝ) / 5}
  have hF : ∀ N, MeasurableSet (F N) := measurableSet_box_failure α
  have hev : ∀ᵐ ω ∂environmentLaw ν, ∀ᶠ N : ℕ in atTop, ω ∉ F N := by
    filter_upwards [hlim] with ω hω
    exact (eventually_uniform_of_speed rfl hα hω).mono (by
      intro N hN
      simpa only [F, mem_ofPred_eq, not_not] using hN)
  have hp : Tendsto (fun N => environmentLaw ν (F N)) atTop (𝓝 0) := by
    simpa only [measure_empty] using
      tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
        (μ := environmentLaw ν) (A := ∅) MeasurableSet.empty hF
        (hev.mono fun ω hω => hω.mono fun N hN => by simpa only [mem_empty_iff_false, iff_false] using hN)
  simpa only [Measure.real_def, ENNReal.toReal_zero, Function.comp_def, F, α] using
    (ENNReal.continuousAt_toReal (x := 0) (by simp)).tendsto.comp hp

end LPPDifferentiability.FinalDraft.FlatBlockSource
