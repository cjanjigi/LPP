/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatClassificationSource.WeightedShapeBeyondEdge
import Differentiability.Probability.HalfLineEdge
import all Differentiability.FinalDraft.FlatTop.OriginEdge
import Differentiability.Model.OrientedPercolationLaws
import LPP_Foundations.Model.LastPassage.Bounds
import Mathlib.Tactic

/-! # Strictness for bounded weights with no atom at one -/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace LPPDifferentiability.FinalDraft

/-- Small positive Bernoulli density forces a negative one-step expected edge. Only the two
possible nonnegative first coordinates at level one can give a nonnegative edge. -/
theorem integral_halfLineEdge_one_lt_zero_of_small_density (q : unitInterval)
    (hq : 0 < (q : ℝ)) (hqSmall : (q : ℝ) < 1 / 4) :
    (∫ ω, (halfLineEdge ω 1 : ℝ) ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0 q)) < 0 := by
  let κ := bernoulliMeasure (1 : ℝ) 0 q
  let E (u : Lattice) := (fun ω : Environment => ω u) ⁻¹' ({1} : Set ℝ)
  let B := E (1, 0) ∪ E (0, 1)
  have hκ : 0 < κ {1} := bernoulli_one_pos_of_density_pos q hq
  have hE (u : Lattice) : MeasurableSet (E u) :=
    measurable_environment_eval u (measurableSet_singleton _)
  have hB : MeasurableSet B := (hE _).union (hE _)
  have hEprob (u : Lattice) : (environmentLaw κ).real (E u) = (q : ℝ) := by
    change (environmentLaw κ).real ((fun ω : Environment => ω u) ⁻¹' {1}) = _
    rw [← map_measureReal_apply (measurable_environment_eval u) (measurableSet_singleton _),
      environmentLaw_map_eval]
    unfold Measure.real
    rw [show κ {1} = (unitInterval.toNNReal q : ENNReal) from
      bernoulliMeasure_apply_of_mem_of_notMem q (measurableSet_singleton _) (by simp) (by simp),
      ENNReal.coe_nnreal_eq, unitInterval.coe_toNNReal, ENNReal.toReal_ofReal q.property.1]
  have hBprob : (environmentLaw κ).real B ≤ 2 * (q : ℝ) := by
    have h := measureReal_union_le (μ := environmentLaw κ) (E (1, 0)) (E (0, 1))
    rw [hEprob, hEprob] at h
    linarith only [h]
  have hbound : ∀ᵐ ω ∂environmentLaw κ,
      (halfLineEdge ω 1 : ℝ) ≤ B.indicator (fun _ => (2 : ℝ)) ω - 1 := by
    filter_upwards [ae_openReachSet_halfLine_infinite κ hκ] with ω hω
    have hmax := halfLineEdge_le ω 1
    by_cases hw : ω ∈ B
    · rw [indicator_of_mem hw]
      exact_mod_cast (show halfLineEdge ω 1 ≤ (2 : ℤ) - 1 from hmax)
    · rw [indicator_of_notMem hw]
      suffices hneg : halfLineEdge ω 1 ≤ -1 by exact_mod_cast hneg
      by_contra! hneg
      have hb : BddAbove (Prod.fst '' openReachSet (topSites ω) antidiagHalfLine 1) := by
        refine ⟨1, ?_⟩
        rintro _ ⟨v, hv, rfl⟩
        simpa only [zero_add, Nat.cast_one] using
          bddAbove_fst_openReachSet _ _ _ 0 (fun u hu => hu.2) v hv
      obtain ⟨v, hv, hvmax⟩ := maxFirst_mem _ (hω 1).nonempty hb
      have hmax' : v.1 = halfLineEdge ω 1 := hvmax
      have hlev : v.1 + v.2 = 1 := by
        have h := openReachSet_subset_levelSet (topSites ω) antidiagHalfLine 0 1
          (fun _ h => h.1) hv
        simpa [levelSet] using h
      have hvOpen : ω v = 1 :=
        ((mem_openReachSet_succ_iff (topSites ω) antidiagHalfLine 0 v).mp hv).1
      have hcase : v.1 = 1 ∨ v.1 = 0 := by omega
      rcases hcase with hv1 | hv0
      · have he : v = ((1, 0) : Lattice) := Prod.ext hv1 (by omega)
        exact hw (Or.inl (he ▸ hvOpen))
      · have he : v = ((0, 1) : Lattice) := Prod.ext hv0 (by omega)
        exact hw (Or.inr (he ▸ hvOpen))
  have hInt : Integrable (B.indicator (fun _ : Environment => (2 : ℝ))) (environmentLaw κ) :=
    (integrable_const (2 : ℝ)).indicator hB
  have hmean := integral_mono_ae (integrable_halfLineEdge κ hκ 1)
    (hInt.sub (integrable_const (1 : ℝ))) hbound
  simp only [Pi.sub_apply] at hmean
  rw [integral_sub hInt (integrable_const (1 : ℝ)), integral_indicator_const _ hB,
    integral_const] at hmean
  simp only [probReal_univ, smul_eq_mul] at hmean
  change (∫ ω, (halfLineEdge ω 1 : ℝ) ∂environmentLaw κ) < 0
  linarith only [hmean, hBprob, hqSmall]

/-- A law bounded above by one with no atom at one has shape strictly below one at every unit
direction. The proof uses a small positive threshold density, or a deterministic weight gap
when that threshold has zero mass. -/
theorem weighted_shape_lt_one_of_atom_one_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ w ∂ν, w ≤ 1) (hp : ν {1} = 0) (g : Quadrant → ℝ)
    (hcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (s : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    g (toQuadrant (s, 1 - s)) < 1 := by
  have hT := tendsto_nearTopDensity ν hle
  have hR := continuous_subtype_val.continuousAt.tendsto.comp hT
  have hzero : ν.real {1} = 0 := by rw [Measure.real_def, hp, ENNReal.toReal_zero]
  change Tendsto (fun n : ℕ => (nearTopDensity ν (1 / ((n : ℝ) + 1)) : ℝ))
    atTop (𝓝 (ν.real {1})) at hR
  rw [hzero] at hR
  obtain ⟨n, hn⟩ := (hR.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).exists
  let τ : ℝ := 1 / ((n : ℝ) + 1)
  have hτ : 0 < τ := by positivity
  let q := nearTopDensity ν τ
  by_cases hq : 0 < (q : ℝ)
  · let m : ℝ := ∫ ω, (halfLineEdge ω 1 : ℝ) ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0 q)
    have hm : m < 0 := integral_halfLineEdge_one_lt_zero_of_small_density q hq hn
    exact weighted_shape_lt_one_of_threshold_mean ν hle τ hτ hq g hcont hhom hshape
      (m / 2) 1 Nat.one_pos (by
        change m < (m / 2) * (↑(1 : ℕ) : ℝ)
        rw [Nat.cast_one, mul_one]
        linarith only [hm])
      s (by linarith) hs₀ hs₁
  · have hq0 : (q : ℝ) = 0 := le_antisymm (not_lt.mp hq) q.property.1
    have hμ : ν (Ici (1 - τ)) = 0 := by
      change (ν (Ici (1 - τ))).toReal = 0 at hq0
      exact ((ENNReal.toReal_eq_zero_iff _).mp hq0).resolve_right (measure_ne_top _ _)
    have hau : ∀ᵐ w ∂ν, w ≤ 1 - τ := ae_iff.mpr
      (measure_mono_null (fun _ h => (lt_of_not_ge h).le) hμ)
    have hEnv : ∀ᵐ ω ∂environmentLaw ν, ∀ z : Lattice, ω z ≤ 1 - τ :=
      ae_all_iff.mpr fun z =>
        ae_of_ae_map (measurable_environment_eval z).aemeasurable
          (by rwa [environmentLaw_map_eval ν z])
    obtain ⟨ω, hω, hs⟩ := (hEnv.and hshape).exists
    have hlow : ∀ᶠ m : ℕ in atTop,
        lastPassage ω 0 (⌊s * (m : ℝ)⌋₊, m - ⌊s * (m : ℝ)⌋₊) < (1 - τ / 2) * m := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
      have hfloor : ⌊s * (m : ℝ)⌋₊ ≤ m :=
        Nat.floor_le_of_le (mul_le_of_le_one_left (Nat.cast_nonneg _) hs₁)
      have hlev := Nat.add_sub_of_le hfloor
      have h := lastPassage_le_const ω 0 (⌊s * (m : ℝ)⌋₊, m - ⌊s * (m : ℝ)⌋₊) _ hω
      change _ ≤ (↑(⌊s * (m : ℝ)⌋₊ + (m - ⌊s * (m : ℝ)⌋₊)) : ℝ) * (1 - τ) at h
      rw [hlev] at h
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      nlinarith [mul_pos hτ hmR]
    exact (weighted_shape_le_of_eventually_low g hcont hhom s (τ / 2) hs₀ hs₁ ω hs hlow)
      |>.trans_lt (by linarith)

end LPPDifferentiability.FinalDraft
