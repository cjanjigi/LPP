/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.SupportTilt
public import Busemann.Finite.PotentialOrder
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Martin2004.Shape.ExpectedRateShape
public import ProbabilityBasics.Probability.AbsoluteMomentTail
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import Martin2004.Shape.ExpectedRateUniform
import Busemann.Geometry.SupportIdentities
import Martin2004.Analysis.RationalPassageNormalization
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Approximation of the actual finite tilted maximum in JR1810.03580v3,
proof of Theorem 4.8 near equation (4.17). -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal NNReal Topology

namespace LPP.Busemann

private theorem potential_real_le_iff (ω : Environment) (h : ℝ × ℝ)
    (n : ℕ) (r : ℝ) :
    (finiteTiltedPotential ω h 0 (n : ℤ)).toReal ≤ r ↔
      ∀ k : Fin (n + 1), lastPassage ω 0 (k.val, n - k.val) +
        h.1 * (k.val : ℝ) + h.2 * ((n - k.val : ℕ) : ℝ) ≤ r := by
  have hactive : (0 : Lattice).1 + (0 : Lattice).2 ≤ (n : ℤ) := by simp
  have hcoe := EReal.coe_toReal
    (finiteTiltedPotential_ne_top ω h 0 n hactive)
    (finiteTiltedPotential_ne_bot ω h 0 n hactive)
  rw [← EReal.coe_le_coe_iff, hcoe]
  have hlen : ((n : ℤ) - ((0 : Lattice).1 + (0 : Lattice).2)).toNat = n := by simp
  have hapi := finiteTiltedPotential_le_coe_iff ω h 0 (n : ℤ) hactive r
  rw [hlen] at hapi
  exact hapi

private theorem candidate_le_potential_real (ω : Environment) (h : ℝ × ℝ)
    (n : ℕ) (k : Fin (n + 1)) :
    lastPassage ω 0 (k.val, n - k.val) + h.1 * (k.val : ℝ) +
      h.2 * ((n - k.val : ℕ) : ℝ) ≤
        (finiteTiltedPotential ω h 0 (n : ℤ)).toReal :=
  (potential_real_le_iff ω h n _).mp le_rfl k

/-- The change in the actual finite tilted maximum is bounded by the largest
passage change on its diagonal. The same deterministic tilt cancels, as in
JR1810.03580v3, proof of Theorem 4.8. -/
theorem finiteTiltedPotential_sub_abs_le_passage_sup
    (ω η : Environment) (h : ℝ × ℝ) (n : ℕ) :
    |(finiteTiltedPotential ω h 0 (n : ℤ)).toReal -
      (finiteTiltedPotential η h 0 (n : ℤ)).toReal| ≤
      Finset.univ.sup' Finset.univ_nonempty (fun k : Fin (n + 1) =>
        |lastPassage ω 0 (k.val, n - k.val) -
          lastPassage η 0 (k.val, n - k.val)|) := by
  classical
  let D := Finset.univ.sup' Finset.univ_nonempty (fun k : Fin (n + 1) =>
    |lastPassage ω 0 (k.val, n - k.val) - lastPassage η 0 (k.val, n - k.val)|)
  have hD (k : Fin (n + 1)) :
      |lastPassage ω 0 (k.val, n - k.val) -
        lastPassage η 0 (k.val, n - k.val)| ≤ D :=
    Finset.le_sup' (fun j : Fin (n + 1) =>
      |lastPassage ω 0 (j.val, n - j.val) - lastPassage η 0 (j.val, n - j.val)|)
      (Finset.mem_univ k)
  have hforward : (finiteTiltedPotential ω h 0 (n : ℤ)).toReal ≤
      (finiteTiltedPotential η h 0 (n : ℤ)).toReal + D := by
    apply (potential_real_le_iff ω h n _).mpr
    intro k
    have hdiff := (abs_le.mp (hD k)).2
    have hcand := candidate_le_potential_real η h n k
    linarith only [hdiff, hcand]
  have hbackward : (finiteTiltedPotential η h 0 (n : ℤ)).toReal ≤
      (finiteTiltedPotential ω h 0 (n : ℤ)).toReal + D := by
    apply (potential_real_le_iff η h n _).mpr
    intro k
    have hdiff := (abs_le.mp (hD k)).1
    have hcand := candidate_le_potential_real ω h n k
    linarith only [hdiff, hcand]
  exact abs_le.mpr ⟨by linarith only [hbackward], by linarith only [hforward]⟩

/-- Under the native absolute moment, the actual finite tilted potential at a
supporting tilt has zero almost-sure normalized limit. The proof uses uniform
shape and an actual contact endpoint on each diagonal, as required near
JR1810.03580v3, equation (4.17). -/
theorem ae_finiteTiltedPotential_div_tendsto_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧ (∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) (h : SupportTilt g) :
    ∀ᵐ ω ∂environmentLaw μ, Tendsto (fun n : ℕ =>
      (finiteTiltedPotential ω h.val 0 (n : ℤ)).toReal / (n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨p, hp, hpMoment⟩ := hmoment
  have hpos := (ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
    μ hp hpMoment).2
  have hneg := ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment
    μ hp hpMoment
  obtain ⟨hcont, hhom, hshape⟩ := ae_uniform_of_isExpectedRateShape μ hneg hpos hg
  obtain ⟨ξ, hsupp⟩ := h.property
  obtain ⟨hmajor, hcontact⟩ :=
    (supportsAt_iff_through_origin_majorant_and_contact g ξ h.val
      (fun c z => hhom c z)).mp hsupp
  let k : ℕ → ℕ := fun n => ⌊(n : ℝ) * (ξ.val.1 : ℝ)⌋₊
  have hξsum : (ξ.val.1 : ℝ) + (ξ.val.2 : ℝ) = 1 := ξ.property.2.2
  have hkle (n : ℕ) : k n ≤ n := by
    apply Nat.floor_le_of_le
    have hξ2 : 0 ≤ (ξ.val.2 : ℝ) := ξ.val.2.property
    have hξle : (ξ.val.1 : ℝ) ≤ 1 := by linarith only [hξsum, hξ2]
    exact mul_le_of_le_one_right (Nat.cast_nonneg n) hξle
  have hkdiv : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ)) atTop
      (𝓝 (ξ.val.1 : ℝ)) :=
    tendsto_nat_floor_mul_div_nat _ ξ.val.1.property
  have hsecond : Tendsto (fun n : ℕ => ((n - k n : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 (ξ.val.2 : ℝ)) := by
    have hlim := (tendsto_const_nhds.sub hkdiv : Tendsto
      (fun n : ℕ => 1 - (k n : ℝ) / (n : ℝ)) atTop (𝓝 (1 - (ξ.val.1 : ℝ))))
    have heq : 1 - (ξ.val.1 : ℝ) = (ξ.val.2 : ℝ) := by linarith only [hξsum]
    rw [heq] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Nat.cast_sub (hkle n)]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
  let q : ℕ → Quadrant := fun n =>
    ((n : ℝ≥0)⁻¹ * (k n : ℝ≥0), (n : ℝ≥0)⁻¹ * (n - k n : ℕ))
  have hq : Tendsto q atTop (𝓝 ξ.val) := by
    apply Tendsto.prodMk_nhds
    · apply NNReal.tendsto_coe.mp
      simpa only [q, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_inv, NNReal.coe_natCast,
        inv_mul_eq_div] using hkdiv
    · apply NNReal.tendsto_coe.mp
      simpa only [q, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_inv, NNReal.coe_natCast,
        inv_mul_eq_div] using hsecond
  let A : ℕ → ℝ := fun n => g (q n) +
    h.val.1 * ((k n : ℝ) / (n : ℝ)) +
    h.val.2 * (((n - k n : ℕ) : ℝ) / (n : ℝ))
  have hA : Tendsto A atTop (𝓝 0) := by
    have ht := (((hcont.tendsto ξ.val).comp hq).add
      (hkdiv.const_mul h.val.1)).add (hsecond.const_mul h.val.2)
    have hz : g ξ.val + h.val.1 * (ξ.val.1 : ℝ) +
        h.val.2 * (ξ.val.2 : ℝ) = 0 := by linarith only [hcontact]
    rw [hz] at ht
    exact ht
  have hAeq (n : ℕ) : A n =
      (g ((k n : ℝ≥0), ((n - k n : ℕ) : ℝ≥0)) +
        h.val.1 * (k n : ℝ) + h.val.2 * ((n - k n : ℕ) : ℝ)) / (n : ℝ) := by
    have hs := hhom ((n : ℝ≥0)⁻¹)
      ((k n : ℝ≥0), ((n - k n : ℕ) : ℝ≥0))
    change g (q n) = _ at hs
    dsimp only [A]
    rw [hs, NNReal.coe_inv, NNReal.coe_natCast]
    ring
  filter_upwards [hshape] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hω (ε / 3) (by positivity)
  have hsmall := hA.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < ε / 3))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hsmall
  refine ⟨max 1 (max N M), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left 1 _).trans hn
  have hnN : N ≤ n := (le_max_left N M).trans ((le_max_right 1 _).trans hn)
  have hnM : M ≤ n := (le_max_right N M).trans ((le_max_right 1 _).trans hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hupper : (finiteTiltedPotential ω h.val 0 (n : ℤ)).toReal ≤ ε / 3 * n := by
    apply (potential_real_le_iff ω h.val n _).mpr
    intro j
    have hlength : j.val + (n - j.val) = n := by omega
    have herr := hN (j.val, n - j.val) (by simpa only [hlength] using hnN)
    have hm := hmajor ((j.val : ℝ≥0), ((n - j.val : ℕ) : ℝ≥0))
    simp only [NNReal.coe_natCast] at hm
    change |lastPassage ω 0 (j.val, n - j.val) -
      g ((j.val : ℝ≥0), ((n - j.val : ℕ) : ℝ≥0))| ≤
        ε / 3 * ((j.val + (n - j.val) : ℕ) : ℝ) at herr
    rw [hlength] at herr
    linarith only [(abs_le.mp herr).2, hm]
  have hlength : k n + (n - k n) = n := Nat.add_sub_of_le (hkle n)
  have herr := hN (k n, n - k n) (by simpa only [hlength] using hnN)
  change |lastPassage ω 0 (k n, n - k n) -
    g ((k n : ℝ≥0), ((n - k n : ℕ) : ℝ≥0))| ≤
      ε / 3 * ((k n + (n - k n) : ℕ) : ℝ) at herr
  rw [hlength] at herr
  have hcand := candidate_le_potential_real ω h.val n ⟨k n, by have := hkle n; omega⟩
  have hlower : A n - ε / 3 ≤
      (finiteTiltedPotential ω h.val 0 (n : ℤ)).toReal / (n : ℝ) := by
    have hlo := (abs_le.mp herr).1
    have hraw : g ((k n : ℝ≥0), ((n - k n : ℕ) : ℝ≥0)) +
        h.val.1 * (k n : ℝ) + h.val.2 * ((n - k n : ℕ) : ℝ) -
          ε / 3 * (n : ℝ) ≤
          (finiteTiltedPotential ω h.val 0 (n : ℤ)).toReal := by
      change lastPassage ω 0 (k n, n - k n) +
        h.val.1 * (k n : ℝ) + h.val.2 * ((n - k n : ℕ) : ℝ) ≤ _ at hcand
      linarith only [hlo, hcand]
    calc
      A n - ε / 3 =
          (g ((k n : ℝ≥0), ((n - k n : ℕ) : ℝ≥0)) +
            h.val.1 * (k n : ℝ) + h.val.2 * ((n - k n : ℕ) : ℝ) -
              ε / 3 * (n : ℝ)) / (n : ℝ) := by
        rw [hAeq]
        field_simp [ne_of_gt hnpos]
      _ ≤ _ := div_le_div_of_nonneg_right hraw hnpos.le
  have hAn : |A n| < ε / 3 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hM n hnM
  rw [Real.dist_eq, sub_zero]
  apply abs_lt.mpr
  constructor
  · have hlowA := (abs_lt.mp hAn).1
    linarith only [hlower, hlowA, hε]
  · have hup := (div_le_iff₀ hnpos).mpr hupper
    linarith only [hup, hε]

end LPP.Busemann
