/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.Grid.GeneralEvents
public import Differentiability.FinalDraft.StairGeometry.Event
public import Differentiability.Probability.FiniteHeavyVertices
import all Differentiability.Probability.StairGeometryEvent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! The global heavy-vertex bound of the final differentiability draft
(subsection `sub:ub_mom-chat` and Lemma `lem:heavy`), at a general power of the width. -/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LPPDifferentiability.FinalDraft

/-- The polynomial loss from the logarithmic cutoff is dominated by the
strict gap between the moment order and (1+\gamma). -/
theorem tendsto_global_heavy_scale_zero (p gamma : ℝ) (hp : 1 + gamma < p) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) ^ p *
      ((2 : ℝ) ^ k) ^ (1 + gamma - p)) atTop (𝓝 0) := by
  let b := (p - (1 + gamma)) * Real.log 2
  have hb : 0 < b := mul_pos (sub_pos.mpr hp) (Real.log_pos (by norm_num))
  have hx : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p b hb).comp hx
  have hscaled := hlim.const_mul (Real.exp b)
  simp only [Function.comp_def, mul_zero] at hscaled
  refine hscaled.congr fun k => ?_
  have hpow : ((2 : ℝ) ^ k) ^ (1 + gamma - p) = Real.exp (-b * (k : ℝ)) := by
    rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    dsimp [b]
    ring
  rw [hpow, show -b * (k : ℝ) = b + (-b * ((k : ℝ) + 1)) by ring, Real.exp_add]
  ring

/-- On the actual working region, the probability of any weight above
`c * s_k / (k + 1)` tends to zero when the characteristic length is at most
`s_k ^ gamma` and the positive moment order exceeds `1 + gamma`. The region
and length bound are kept on the same record set. -/
theorem working_region_upper_cap_failure_tendsto_of_length_power
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p gamma : ℝ) (hgamma : 0 ≤ gamma) (hp : 1 + gamma < p)
    (hmom : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (a A R C₁ c : ℝ) (hA : 0 < A) (hR : 0 < R) (hC₁ : 0 ≤ C₁) (hc : 0 < c)
    (m : ℕ → ℕ) (records : Set ℕ)
    (hLength : ∀ᶠ k : ℕ in atTop ⊓ 𝓟 records,
      (2 : ℝ) ^ m k ≤ ((2 : ℝ) ^ k) ^ gamma) :
    Tendsto (fun k : ℕ => (environmentLaw μ).real
      (gridUpperCap (StairGeometry.workingRegion a A R C₁ m k)
        (c * (2 : ℝ) ^ k / ((k : ℝ) + 1)))ᶜ) (atTop ⊓ 𝓟 records) (𝓝 0) := by
  classical
  let F : Filter ℕ := atTop ⊓ 𝓟 records
  let M : ℝ := ∫ x : ℝ, (max x 0) ^ p ∂μ
  let K : ℝ := (2 * A + 13) * (2 * R + 4 * C₁ + 25)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hM : 0 ≤ M := integral_nonneg fun x => Real.rpow_nonneg (le_max_right x 0) p
  have hp0 : 0 < p := by linarith
  have hlim : Tendsto (fun k : ℕ => K * M * c ^ (-p) *
      (((k : ℝ) + 1) ^ p * ((2 : ℝ) ^ k) ^ (1 + gamma - p))) F (𝓝 0) := by
    simpa only [mul_zero] using ((tendsto_global_heavy_scale_zero p gamma hp).mono_left
      (show F ≤ atTop from inf_le_left)).const_mul (K * M * c ^ (-p))
  refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hlim
  filter_upwards [hLength] with k hk
  let s : ℝ := (2 : ℝ) ^ k
  let ell : ℝ := (2 : ℝ) ^ m k
  let levelRadius : ℝ := (A + 5) * ell
  let width : ℝ := (R + 2 * C₁ + 10) * s
  let count : ℝ := (k : ℝ) + 1
  let cutoff := c * s / count
  have hs : 1 ≤ s := one_le_pow₀ (by norm_num)
  have hell : 1 ≤ ell := one_le_pow₀ (by norm_num)
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hcount : 0 < count := by dsimp [count]; positivity
  have hcutoff : 0 < cutoff := div_pos (mul_pos hc hs0) hcount
  have hrad : 0 ≤ levelRadius := by dsimp [levelRadius]; positivity
  have hw : 0 ≤ width := by dsimp [width]; positivity
  obtain ⟨hf, hfinite⟩ := boxS_finite_ncard_le a levelRadius width hrad hw
  let Q := hf.toFinset
  have hQ (z : Lattice) : z ∈ Q ↔ z ∈ StairGeometry.workingRegion a A R C₁ m k := by
    rw [Set.Finite.mem_toFinset]
    rfl
  have hcard₀ : (Q.card : ℝ) ≤ (2 * levelRadius + 3) * (2 * width + 5) := by
    simpa only [Q, ← Set.ncard_eq_toFinset_card _ hf] using hfinite
  have hlevel_le : 2 * levelRadius + 3 ≤ (2 * A + 13) * ell := by
    dsimp [levelRadius]
    nlinarith only [hell]
  have hwidth_le : 2 * width + 5 ≤ (2 * R + 4 * C₁ + 25) * s := by
    dsimp [width]
    nlinarith only [hs]
  have hcard : (Q.card : ℝ) ≤ K * s ^ (1 + gamma) := by
    calc
      _ ≤ _ := hcard₀
      _ ≤ ((2 * A + 13) * ell) * ((2 * R + 4 * C₁ + 25) * s) :=
        mul_le_mul hlevel_le hwidth_le (by positivity) (by positivity)
      _ = (K * s) * ell := by dsimp [K]; ring
      _ ≤ (K * s) * s ^ gamma := mul_le_mul_of_nonneg_left hk (mul_nonneg hK hs0.le)
      _ = _ := by rw [Real.rpow_add hs0, Real.rpow_one]; ring
  have hevent : (gridUpperCap (StairGeometry.workingRegion a A R C₁ m k) cutoff)ᶜ =
      {ω : Environment | ∃ z ∈ Q, cutoff < ω z} := by
    ext ω
    simp only [gridUpperCap, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le, exists_prop, hQ]
  have hMarkov := (measureReal_exists_upper_heavy_site_le_and_safe_ge μ hp0 hmom cutoff hcutoff Q).2.1
  have hpow : cutoff ^ (-p) = c ^ (-p) * s ^ (-p) * count ^ p := by
    dsimp only [cutoff]
    rw [Real.div_rpow (mul_nonneg hc.le hs0.le) hcount.le, Real.mul_rpow hc.le hs0.le,
      Real.rpow_neg hcount.le, div_inv_eq_mul]
  change (environmentLaw μ).real
    (gridUpperCap (StairGeometry.workingRegion a A R C₁ m k) cutoff)ᶜ ≤
      K * M * c ^ (-p) * (count ^ p * s ^ (1 + gamma - p))
  rw [hevent]
  calc
    _ ≤ (Q.card : ℝ) * M * cutoff ^ (-p) := hMarkov
    _ ≤ (K * s ^ (1 + gamma)) * M * cutoff ^ (-p) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hM)
        (Real.rpow_nonneg hcutoff.le _)
    _ = _ := by
      have hsum : s ^ (1 + gamma - p) = s ^ (1 + gamma) * s ^ (-p) := by
        rw [← Real.rpow_add hs0]
        congr 1
      rw [hpow, hsum]
      ring

/-- The same estimate applies to the printed denominator `k` in the
working-region cutoff, which is at least as high once `k > 0`. -/
theorem working_region_upper_cap_failure_tendsto_of_length_power_at_source_cutoff
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p gamma : ℝ) (hgamma : 0 ≤ gamma) (hp : 1 + gamma < p)
    (hmom : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (a A R C₁ c : ℝ) (hA : 0 < A) (hR : 0 < R) (hC₁ : 0 ≤ C₁) (hc : 0 < c)
    (m : ℕ → ℕ) (records : Set ℕ)
    (hLength : ∀ᶠ k : ℕ in atTop ⊓ 𝓟 records,
      (2 : ℝ) ^ m k ≤ ((2 : ℝ) ^ k) ^ gamma) :
    Tendsto (fun k : ℕ => (environmentLaw μ).real
      (gridUpperCap (StairGeometry.workingRegion a A R C₁ m k)
        (c * (2 : ℝ) ^ k / (k : ℝ)))ᶜ) (atTop ⊓ 𝓟 records) (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    (working_region_upper_cap_failure_tendsto_of_length_power μ p gamma hgamma hp hmom
      a A R C₁ c hA hR hC₁ hc m records hLength)
  filter_upwards [(eventually_gt_atTop (0 : ℕ)).filter_mono
    (show atTop ⊓ 𝓟 records ≤ atTop from inf_le_left)] with k hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcutoff : c * (2 : ℝ) ^ k / ((k : ℝ) + 1) ≤ c * (2 : ℝ) ^ k / (k : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hkR (by linarith)
  exact measureReal_mono (μ := environmentLaw μ) (fun ω hω hsmall =>
    hω (fun z hz => (hsmall z hz).trans hcutoff))

end LPPDifferentiability.FinalDraft
