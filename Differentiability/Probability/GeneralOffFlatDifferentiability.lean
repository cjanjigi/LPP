/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.CharacteristicLengths
public import ProbabilityBasics.Probability.PositiveMomentTail
public import Differentiability.Probability.GridSimultaneousGeneral
public import Differentiability.Probability.ArbitraryEndpointsGeneral
public import Differentiability.Probability.BlockDefectRarityOfEndpoints
public import Differentiability.Probability.CornerExclusionGeneral
public import Differentiability.Analysis.DirectionalAssembly
import Mathlib.Tactic

/-!
# Differentiability away from the flat segment for general weights

For a continuous, homogeneous, concave function with the almost-sure shape property, this file
proves differentiability at directions where the top-weight shape is below one, under moment
assumptions (A2) and (A3). The proof uses record scales, a simultaneous grid estimate, an
arbitrary-endpoint estimate and the one-step bound for unbounded weights.

## Main results

- `differentiableAt_of_off_flat_general`: differentiability at a direction away from the flat
  segment under (A2) and (A3).

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, Theorem 2.1, Sections 6.2 and 6.5, and Appendix B.4,
  preprint.
-/

public section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- The constant `q0 = (1/120)^32 / 2` satisfies `60 (2 q0)^(1/32) ≤ 1/2`, as required by
equation (6.1) of the differentiability preprint. -/
private theorem exists_q0_general :
    ∃ q0 : ℝ, 0 < q0 ∧ q0 < 1 ∧ 60 * (2 * q0) ^ (1 / 32 : ℝ) ≤ 1 / 2 := by
  refine ⟨(1 / 120 : ℝ) ^ 32 / 2, by positivity, ?_, ?_⟩
  · have : (1 / 120 : ℝ) ^ 32 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  · have h : 2 * ((1 / 120 : ℝ) ^ 32 / 2) = (1 / 120 : ℝ) ^ 32 := by ring
    rw [h]
    have h2 : ((1 / 120 : ℝ) ^ 32) ^ (1 / 32 : ℝ) = 1 / 120 := by
      have := Real.pow_rpow_inv_natCast (x := (1 / 120 : ℝ)) (n := 32) (by norm_num)
        (by norm_num)
      simpa using this
    rw [h2]
    norm_num

/-- The bound in equation (6.6) of the differentiability preprint holds for every `s ≥ 1` when
`η ≤ 1`. -/
private theorem rare_K_of_one_le_general (dl dr η s : ℝ) (hη : η ≤ 1) (hs : 1 ≤ s) :
    3 * η * s + |(dl + dr) / 2| * (2 * s + 2) < 100 * (1 + |dl| + |dr|) * s := by
  have h1 : |(dl + dr) / 2| ≤ (|dl| + |dr|) / 2 := by
    rw [abs_div, abs_two]
    have := abs_add_le dl dr
    linarith
  have hA := abs_nonneg dl
  have hB := abs_nonneg dr
  have h2 : |(dl + dr) / 2| * (2 * s + 2) ≤ (|dl| + |dr|) / 2 * (2 * s + 2) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  have h3 : 3 * η * s ≤ 3 * s := by nlinarith
  nlinarith [mul_nonneg (add_nonneg hA hB) (sub_nonneg.2 hs)]

/-- For `y > 0`, an integer `n ≥ 1` exists with `x < n y`; this supplies the constants in
equation (B.7) of the differentiability preprint once `p'` is fixed. -/
private theorem exists_nat_mul_gt (x y : ℝ) (hy : 0 < y) :
    ∃ n : ℕ, 1 ≤ n ∧ x < (n : ℝ) * y := by
  obtain ⟨n, hn⟩ := exists_nat_gt (x / y)
  refine ⟨n + 1, by omega, ?_⟩
  have h1 : x < n * y := by rwa [div_lt_iff₀ hy] at hn
  push_cast
  nlinarith

/-- **Theorem 2.1 (`thm:main`) away from the flat segment, for general weights.** Under the
negative-part moment assumption (A2) with order greater than `1` and positive-part moment
assumption (A3) with order greater than `4`, a continuous, homogeneous, concave function with
the almost-sure shape property is differentiable at every direction `(a, 1 - a)` where the
top-weight shape is less than `1`. The proof follows Section 6.5 of the differentiability
preprint and uses the general-weight one-step estimate in Appendix B.4. -/
theorem differentiableAt_of_off_flat_general
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂μ) < ∞)
    (hpos : ∃ ppos : ℝ, 4 < ppos ∧
      (∫⁻ t, ENNReal.ofReal ((max t 0) ^ ppos) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (Gtop : ℝ)
    (htop : Tendsto (fun m : ℕ => (∫ ω : Environment, lastPassage (fun z =>
      if (ω z : EReal) = sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then (1 : ℝ) else 0)
        0 (⌊(m : ℝ) * a⌋₊, ⌊(m : ℝ) * (1 - a)⌋₊) ∂environmentLaw μ) / (m : ℝ))
      atTop (𝓝 Gtop))
    (hgap : Gtop < 1) :
    DifferentiableAt ℝ (quadrantExtension g) (a, 1 - a) := by
  classical
  -- Assumptions (A2) and (A3) give the moment bounds and the positive square-root tail.
  have hsqrt : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ :=
    positive_integrated_sqrt_tail_lt_top_of_full_positive_moment μ hpos
  obtain ⟨p', hp', hmom'⟩ := hneg
  obtain ⟨p, hp, hmomp⟩ := hpos
  have hneg' : ∃ p : ℝ, 1 < p ∧ (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞ :=
    ⟨p', hp', hmom'⟩
  -- Section 6.5 introduces the profile and its one-sided derivatives.
  set H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h) with hH
  set dl : ℝ := derivWithin H (Iio 0) 0 with hdl
  set dr : ℝ := derivWithin H (Ioi 0) 0 with hdr
  by_cases heq : dl = dr
  · exact differentiableAt_quadrantExtension_of_profile_derivWithin_eq g hghom hgconc a ha₀ ha₁
      heq
  exfalso
  -- Concavity gives a positive corner size when the one-sided derivatives differ; equation
  -- (6.14) chooses `η` from that size.
  have hle : dr ≤ dl := profile_rightDeriv_le_leftDeriv g hgconc a ha₀ ha₁
  set c : ℝ := (dl - dr) / 2 with hc
  have hcpos : 0 < c := by
    have : dr < dl := lt_of_le_of_ne hle (Ne.symm heq)
    rw [hc]; linarith
  set η : ℝ := min 1 (c / 2) with hη
  have hη0 : 0 < η := lt_min one_pos (by linarith)
  have hη1 : η ≤ 1 := min_le_left _ _
  set G0 : ℝ := H 0 with hG0
  -- Equation (6.1) fixes `q0`, and Lemma 4.4 provides the record scales.
  obtain ⟨q0, hq0₀, hq0₁, hsmall⟩ := exists_q0_general
  obtain ⟨k0, hk0, m, nk, Kset, hmtop, hclauses, hKinf, hKset, htrial⟩ :=
    characteristic_length_records μ hneg' hsqrt g hgcont hghom hgconc hgshape a ha₀ ha₁ Gtop htop
      hgap q0 hq0₀ hq0₁
  -- Lemma 4.4 gives the bounds on lengths, indices and exceptional probabilities.
  have hm3 : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k := fun k hk => (hclauses k hk).2.2.1
  have hKset' : ∀ k ∈ Kset, k0 ≤ k := fun k hk => (hKset k hk).1
  have hnk : ∀ k : ℕ, k0 ≤ k →
      (2 : ℝ) ^ m k / 2 < nk k ∧ (nk k : ℝ) ≤ 2 ^ m k ∧
        (environmentLaw μ).real {ω : Environment |
          ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = nk k ∧ ∃ q : Path u e,
            (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤
              8 * (2 : ℝ) ^ k) ∧
              g (toQuadrant (a, 1 - a)) * ((nk k : ℕ) : ℝ) -
                100 * (1 + |dl| + |dr|) * (2 : ℝ) ^ k < pathWeight ω q} ≤ q0 :=
    fun k hk => let h := (hclauses k hk).2.2.2.2; ⟨h.1, h.2.1, h.2.2.1⟩
  -- Equation (B.7) supplies the integers `m₁`, `K₁` and `K₂` from `p'`.
  have hp'0 : 0 < p' := lt_trans one_pos hp'
  obtain ⟨m1, hm1, hm1p⟩ := exists_nat_mul_gt 40 p' hp'0
  obtain ⟨K1, hK1, hK1p'⟩ := exists_nat_mul_gt 4 p' hp'0
  obtain ⟨K2, hK2, hK2p⟩ := exists_nat_mul_gt 24 (p' - 1) (by linarith)
  have hK1p : 4 < ((K1 : ℝ) + 1) * p' := by nlinarith
  -- Lemma 5.7 gives the simultaneous grid event for general weights.
  have hgrid := grid_connections_simultaneous_general μ p' hp' hmom' hsqrt p hp hmomp g hgcont
    hghom hgconc hgshape a ha₀ ha₁ q0 hq0₀ k0 hk0 m Kset hm3 hKset' m1 K1 K2 hm1 hK1 hK2 hm1p
    hK1p hK2p htrial
  -- Proposition 5.9 extends the defect bound to arbitrary endpoints.
  have hend := arbitrary_endpoints_defect_le_general μ hneg' hsqrt g hgcont hghom hgconc hgshape
    a ha₀ ha₁ k0 m Kset hmtop hm3 hKset' m1 K1 K2 hm1 hK1 hK2 hgrid
  -- Equation (6.4) bounds the probabilities of the rare block events.
  obtain ⟨k1, hk1⟩ := block_rare_events_le_of_endpoints μ g a q0 hq0₀ k0 m nk Kset hKset' hnk
    hend η hη0
  -- Section B.4, including equation (B.15), sets the excess threshold for corner exclusion.
  obtain ⟨s₁, hs₁⟩ := corner_excluded_at_scale_general μ hneg' hsqrt p hp hmomp g hgcont hghom
    hgconc hgshape a ha₀ ha₁ H hH dl dr c η G0 hdl hdr hc hcpos hη hG0
  -- Equations (6.5) and (6.6) provide the scale inequalities and the constant `K`.
  obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt
    (max 2 (4 * (|G0| + |(dl + dr) / 2|) / η)) (one_lt_two : (1 : ℝ) < 2)
  obtain ⟨n2, hn2⟩ := pow_unbounded_of_one_lt s₁ (one_lt_two : (1 : ℝ) < 2)
  obtain ⟨k, hkK, hkgt⟩ := hKinf.exists_gt (max (max k1 n1) n2)
  have hk1k : k1 ≤ k := (le_max_left _ _).trans ((le_max_left _ _).trans hkgt.le)
  have hn1k : n1 ≤ k := (le_max_right _ _).trans ((le_max_left _ _).trans hkgt.le)
  have hn2k : n2 ≤ k := (le_max_right _ _).trans hkgt.le
  have hs₁le : s₁ ≤ (2 : ℝ) ^ k :=
    hn2.le.trans (pow_le_pow_right₀ (by norm_num) hn2k)
  have hs2 : 2 ≤ (2 : ℝ) ^ k :=
    (le_max_left _ _).trans (hn1.le.trans (pow_le_pow_right₀ (by norm_num) hn1k))
  have hstep : |G0| + |(dl + dr) / 2| + η * (2 : ℝ) ^ k / 4 ≤ η * (2 : ℝ) ^ k / 2 := by
    have h2 : 4 * (|G0| + |(dl + dr) / 2|) / η ≤ (2 : ℝ) ^ k :=
      (le_max_right _ _).trans (hn1.le.trans (pow_le_pow_right₀ (by norm_num) hn1k))
    rw [div_le_iff₀ hη0] at h2
    nlinarith
  have hK : 3 * η * (2 : ℝ) ^ k + |(dl + dr) / 2| * (2 * (2 : ℝ) ^ k + 2) <
      100 * (1 + |dl| + |dr|) * (2 : ℝ) ^ k :=
    rare_K_of_one_le_general dl dr η _ hη1 (by linarith)
  -- Equation (4.6) bounds the characteristic length and hence `n*`.
  have hkK0 : k0 ≤ k := hKset' k hkK
  have hnkle : (nk k : ℝ) ≤ ((2 : ℝ) ^ k) ^ 3 := by
    calc (nk k : ℝ) ≤ 2 ^ m k := (hnk k hkK0).2.1
      _ ≤ 2 ^ (3 * k) := pow_le_pow_right₀ (by norm_num) (hm3 k hkK0)
      _ = ((2 : ℝ) ^ k) ^ 3 := by rw [← pow_mul, mul_comm]
  have hnk1 : 1 ≤ nk k := by
    have h := (hnk k hkK0).1
    have hpow : (1 : ℝ) ≤ 2 ^ m k := one_le_pow₀ (by norm_num)
    have : (0 : ℝ) < nk k := by linarith
    exact_mod_cast this
  -- Lemma 6.8 and Proposition 6.7 give the defect and multiplicity bounds for the final
  -- contradiction in Theorem 2.1.
  exact hs₁ ((2 : ℝ) ^ k) hs₁le (nk k) hnk1 hnkle (100 * (1 + |dl| + |dr|)) q0 hq0₀ hsmall hK
    hstep (hk1 k hkK hk1k)

end LPPDifferentiability
