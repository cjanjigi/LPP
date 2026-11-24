/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatClassificationSource.WeightedPassageDecay
public import LPP_Foundations.Analysis.Quadrant
import all Differentiability.Probability.TopShapeBeyondEdge
import Mathlib.Tactic

/-! # The original-weight shape below one beyond a threshold edge -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace LPPDifferentiability.FinalDraft

private theorem weighted_scaled_point_bound (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (ε δ : ℝ) (ω : Environment) (n k : ℕ) (hnpos : 0 < n)
    (hlp : lastPassage ω 0 (k, n - k) < (1 - δ) * n)
    (hdev : |lastPassage ω 0 (k, n - k) -
        g ((k : ℝ≥0), ((n - k : ℕ) : ℝ≥0))| ≤ ε * (n : ℝ)) :
    g ((k : ℝ≥0) * (n : ℝ≥0)⁻¹, ((n - k : ℕ) : ℝ≥0) * (n : ℝ≥0)⁻¹) ≤ 1 - δ + ε := by
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hscale : ∀ a : ℝ≥0, (n : ℝ≥0) * (a * (n : ℝ≥0)⁻¹) = a := fun a => by
    rw [mul_comm a, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  have hhom : g ((n : ℝ≥0) * ((k : ℝ≥0) * (n : ℝ≥0)⁻¹),
      (n : ℝ≥0) * (((n - k : ℕ) : ℝ≥0) * (n : ℝ≥0)⁻¹)) =
      ((n : ℝ≥0) : ℝ) * g ((k : ℝ≥0) * (n : ℝ≥0)⁻¹,
        ((n - k : ℕ) : ℝ≥0) * (n : ℝ≥0)⁻¹) :=
    hhom (n : ℝ≥0) ((k : ℝ≥0) * (n : ℝ≥0)⁻¹, ((n - k : ℕ) : ℝ≥0) * (n : ℝ≥0)⁻¹)
  rw [hscale, hscale, NNReal.coe_natCast] at hhom
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hup := (abs_le.1 hdev).1
  have hmul : (n : ℝ) * g ((k : ℝ≥0) * (n : ℝ≥0)⁻¹, ((n - k : ℕ) : ℝ≥0) * (n : ℝ≥0)⁻¹) ≤
      (n : ℝ) * (1 - δ + ε) := by linarith
  exact le_of_mul_le_mul_left hmul hnR

/-- The deterministic half of the argument for one environment: if the shape estimate holds
and the passage time to the level-`n` floor point of the direction `(s, 1 - s)` is eventually
below `(1 - δ) n`, then the shape at `(s, 1 - s)` is at most `1 - δ`. -/
theorem weighted_shape_le_of_eventually_low (g : Quadrant → ℝ) (hcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (s δ : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) (ω : Environment)
    (hshape : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (hlow : ∀ᶠ n : ℕ in atTop,
      lastPassage ω 0 (⌊s * (n : ℝ)⌋₊, n - ⌊s * (n : ℝ)⌋₊) < (1 - δ) * n) :
    g (toQuadrant (s, 1 - s)) ≤ 1 - δ := by
  refine _root_.le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hN1, hN⟩ := hshape ε hε
  have hlim := (hcont.tendsto (toQuadrant (s, 1 - s))).comp (floorPoint_tendsto s hs₀ hs₁)
  refine le_of_tendsto hlim ?_
  filter_upwards [hlow, eventually_ge_atTop N] with n hn hnN
  have hnpos : 0 < n := by omega
  have hle : ⌊s * (n : ℝ)⌋₊ ≤ n :=
    Nat.floor_le_of_le (mul_le_of_le_one_left (Nat.cast_nonneg n) hs₁)
  have hlev : ⌊s * (n : ℝ)⌋₊ + (n - ⌊s * (n : ℝ)⌋₊) = n := by omega
  have h := hN (⌊s * (n : ℝ)⌋₊, n - ⌊s * (n : ℝ)⌋₊) (by
    show N ≤ ⌊s * (n : ℝ)⌋₊ + (n - ⌊s * (n : ℝ)⌋₊)
    omega)
  change |lastPassage ω 0 (⌊s * (n : ℝ)⌋₊, n - ⌊s * (n : ℝ)⌋₊) -
      g ((⌊s * (n : ℝ)⌋₊ : ℝ≥0), ((n - ⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ≥0))| ≤
      ε * ((⌊s * (n : ℝ)⌋₊ + (n - ⌊s * (n : ℝ)⌋₊) : ℕ) : ℝ) at h
  rw [hlev] at h
  exact weighted_scaled_point_bound g hhom ε δ ω n _ hnpos hn h

/-- A finite mean bound for a near-top threshold forces the actual shape below one in
directions to its right. -/
theorem weighted_shape_lt_one_of_threshold_mean (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ w ∂ν, w ≤ 1) (τ : ℝ) (hτ : 0 < τ) (hq : 0 < (nearTopDensity ν τ : ℝ))
    (g : Quadrant → ℝ) (hcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (c : ℝ) (L : ℕ) (hL : 0 < L)
    (hc : ∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw
      (bernoulliMeasure (1 : ℝ) 0 (nearTopDensity ν τ)) < c * L)
    (s : ℝ) (hcs : c < s) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    g (toQuadrant (s, 1 - s)) < 1 := by
  -- the intermediate speed
  obtain ⟨s', hcs', hs's⟩ : ∃ s' : ℝ, c < s' ∧ s' < s :=
    ⟨(c + s) / 2, by linarith, by linarith⟩
  obtain ⟨δ, A, B, hδ, hA, hB, hdecay⟩ :=
    weighted_passage_beyond_edge_decay ν hle τ hτ hq c L hL hc s' hcs' (hs's.le.trans hs₁)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, 1 / (s - s') ≤ n₀ := exists_nat_ge _
  -- the bad events along the direction `(s, 1 - s)`
  obtain ⟨E, hE⟩ : ∃ E : ℕ → Set Environment, ∀ n ω, ω ∈ E n ↔
      (1 - δ) * (((⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ) + ((n - ⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ)) ≤
        lastPassage ω 0 (⌊s * (n : ℝ)⌋₊, n - ⌊s * (n : ℝ)⌋₊) :=
    ⟨fun n => {ω | (1 - δ) * (((⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ) +
        ((n - ⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ)) ≤
      lastPassage ω 0 (⌊s * (n : ℝ)⌋₊, n - ⌊s * (n : ℝ)⌋₊)}, fun _ _ => Iff.rfl⟩
  have hbound : ∀ n : ℕ, n₀ ≤ n →
      (environmentLaw ν).real (E n) ≤ A * Real.exp (-(B * (n : ℝ))) := by
    intro n hn
    have hcast := floor_level_cast s hs₁ n
    have hgap : 1 ≤ (n : ℝ) * (s - s') := by
      have h1 : 1 / (s - s') ≤ (n : ℝ) := le_trans hn₀ (by exact_mod_cast hn)
      exact (div_le_iff₀ (sub_pos.2 hs's)).1 h1
    have hfl := Nat.lt_floor_add_one (s * (n : ℝ))
    have hcond : s' * (((⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ) + ((n - ⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ)) ≤
        ((⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ) := by
      rw [hcast]
      nlinarith
    have hmain := hdecay ⌊s * (n : ℝ)⌋₊ (n - ⌊s * (n : ℝ)⌋₊) hcond
    have hEeq : E n = {ω | (1 - δ) * (((⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ) +
        ((n - ⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ)) ≤
        lastPassage ω 0 (⌊s * (n : ℝ)⌋₊, n - ⌊s * (n : ℝ)⌋₊)} := by
      ext ω
      exact hE n ω
    have hmain' : (environmentLaw ν).real (E n) ≤
        A * Real.exp (-(B * (((⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ) +
          ((n - ⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ)))) := by
      rw [hEeq]
      exact hmain
    rwa [hcast] at hmain'
  -- summability of the bounds
  have hsum_real : Summable (fun n : ℕ => A * Real.exp (-(B * ((n + n₀ : ℕ) : ℝ)))) := by
    have hgeom : Summable (fun n : ℕ => A * Real.exp (-(B * (n : ℝ)))) := by
      have hr : Real.exp (-B) < 1 := by
        have h := Real.exp_lt_exp.2 (show -B < 0 by linarith)
        rwa [Real.exp_zero] at h
      have hs := (summable_geometric_of_lt_one (Real.exp_pos (-B)).le hr).mul_left A
      refine hs.congr fun n => ?_
      have hexp : -(B * (n : ℝ)) = (n : ℝ) * -B := by ring
      rw [hexp, Real.exp_nat_mul]
    exact (summable_nat_add_iff n₀).2 hgeom
  have hsum : ∑' n : ℕ, (environmentLaw ν) (E (n + n₀)) ≠ ∞ := by
    have hle : ∀ n : ℕ, (environmentLaw ν) (E (n + n₀)) ≤
        ENNReal.ofReal (A * Real.exp (-(B * ((n + n₀ : ℕ) : ℝ)))) := by
      intro n
      calc (environmentLaw ν) (E (n + n₀))
          = ENNReal.ofReal ((environmentLaw ν).real (E (n + n₀))) :=
            (ofReal_measureReal (measure_ne_top _ _)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (hbound _ (Nat.le_add_left _ _))
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg hA.le (Real.exp_pos _).le) hsum_real]
    exact ENNReal.ofReal_ne_top
  -- Borel-Cantelli
  have hae1 := ae_eventually_notMem hsum
  have hae2 : ∀ᵐ ω ∂environmentLaw ν, ∀ᶠ n : ℕ in atTop,
      lastPassage ω 0 (⌊s * (n : ℝ)⌋₊, n - ⌊s * (n : ℝ)⌋₊) < (1 - δ) * n := by
    filter_upwards [hae1] with ω hω
    obtain ⟨m, hm⟩ := eventually_atTop.1 hω
    refine eventually_atTop.2 ⟨m + n₀, fun n hn => ?_⟩
    have h := hm (n - n₀) (by omega)
    have hn' : n - n₀ + n₀ = n := by omega
    rw [hn'] at h
    refine not_le.1 (fun h' => h ((hE n ω).2 ?_))
    rw [floor_level_cast s hs₁ n]
    exact h'
  obtain ⟨ω, hω1, hω2⟩ := (hae2.and hshape).exists
  have hfinal := weighted_shape_le_of_eventually_low g hcont hhom s δ hs₀ hs₁ ω hω2 hω1
  linarith

end LPPDifferentiability.FinalDraft
