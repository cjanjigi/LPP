/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.CharacteristicLengths
public import Differentiability.Probability.GridSimultaneous
public import Differentiability.Probability.BlockDefectRarity
public import Differentiability.Probability.CornerExclusion
public import Differentiability.Analysis.DirectionalAssembly
import Mathlib.Tactic

/-!
# Differentiability for bounded weights off the flat segment

Theorem 2.1 of the differentiability preprint for bounded weights, following Section 6.5 of the
preprint with the scale of Section 6.2. At a direction
`(a, 1 - a)` with `Gtop < 1` (off the flat segment) and bounded weights, the one-sided
derivatives of the profile `H h = g (a + h, 1 - a - h)` at `0` are equal, by contradiction with a
corner `c = (dl - dr) / 2 > 0`: choose `η = min 1 (c / 2)`, a constant `q0` with
`60 (2 q0)^(1/32) ≤ 1/2`, the record scales of `characteristic_length_records`, the
simultaneous grid event, the rare block events at a large record index, and apply the corner
exclusion at that scale. The second theorem passes from the open segment to the open quadrant.

## References

* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in the
  planar corner growth model*, preprint, Theorem 2.1, Sections 6.2 and 6.5.
-/

public section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- The constant `q0 = (1/120)^32 / 2` satisfies `60 (2 q0)^(1/32) ≤ 1/2` ((6.1) of the
differentiability preprint). -/
private theorem exists_q0 : ∃ q0 : ℝ, 0 < q0 ∧ q0 < 1 ∧ 60 * (2 * q0) ^ (1 / 32 : ℝ) ≤ 1 / 2 := by
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

/-- Inequality (6.6) of the differentiability preprint: it holds for every `s ≥ 1`, with `η ≤ 1`. -/
private theorem rare_K_of_one_le (dl dr η s : ℝ) (hη : η ≤ 1) (hs : 1 ≤ s) :
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

/-- **Theorem 2.1 of the differentiability preprint for bounded weights at a direction off the flat
segment.** If the weights are
almost surely bounded by `M`, `g` is the shape function, and the direction `(a, 1 - a)` is off
the flat segment (`htop`, `hgap`: the top-weight shape `Gtop < 1`), then the quadrant extension of
`g` is differentiable at `(a, 1 - a)`. -/
theorem differentiableAt_of_bounded_off_flat
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (M : ℝ) (hb : ∀ᵐ x ∂μ, |x| ≤ M)
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
  obtain ⟨hneg, hpos⟩ := bounded_law_negative_moment_and_positive_sqrt_tail μ ⟨M, hb⟩
  set H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h) with hH
  set dl : ℝ := derivWithin H (Iio 0) 0 with hdl
  set dr : ℝ := derivWithin H (Ioi 0) 0 with hdr
  by_cases heq : dl = dr
  · exact differentiableAt_quadrantExtension_of_profile_derivWithin_eq g hghom hgconc a ha₀ ha₁
      heq
  exfalso
  -- A corner: `dr < dl` by concavity of the profile.
  have hle : dr ≤ dl := profile_rightDeriv_le_leftDeriv g hgconc a ha₀ ha₁
  set c : ℝ := (dl - dr) / 2 with hc
  have hcpos : 0 < c := by
    have : dr < dl := lt_of_le_of_ne hle (Ne.symm heq)
    rw [hc]; linarith
  set η : ℝ := min 1 (c / 2) with hη
  have hη0 : 0 < η := lt_min one_pos (by linarith)
  have hη1 : η ≤ 1 := min_le_left _ _
  set G0 : ℝ := H 0 with hG0
  -- The weight bound, made positive.
  set M0 : ℝ := max M 1 with hM0def
  have hM0pos : 0 < M0 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hb0 : ∀ᵐ x ∂μ, |x| ≤ M0 := hb.mono fun x hx => hx.trans (le_max_left _ _)
  have hbup : ∀ᵐ x ∂μ, x ≤ M0 := hb0.mono fun x hx => (le_abs_self x).trans hx
  -- The constant `q0` and the record scales ((6.1) and Lemma 4.4 of the preprint).
  obtain ⟨q0, hq0₀, hq0₁, hsmall⟩ := exists_q0
  obtain ⟨k0, hk0, m, nk, Kset, hmtop, hclauses, hKinf, hKset, htrial⟩ :=
    characteristic_length_records μ hneg hpos g hgcont hghom hgconc hgshape a ha₀ ha₁ Gtop htop
      hgap q0 hq0₀ hq0₁
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
  -- The simultaneous grid event (Lemma 5.7), then the rare block events ((6.4)).
  have hgrid := grid_connections_simultaneous μ hM0pos hb0 hneg hpos g hgcont hghom hgconc
    hgshape a ha₀ ha₁ q0 hq0₀ k0 hk0 m Kset hm3 hKset' htrial
  obtain ⟨k1, hk1⟩ := block_rare_events_le μ hneg hpos g hgcont hghom hgconc hgshape a ha₀ ha₁
    q0 hq0₀ k0 m nk Kset hmtop hm3 hKset' hnk hgrid η hη0
  -- A scale index large enough for (6.5).
  obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt
    (max 2 (2 * (|G0| + |(dl + dr) / 2| + M0) / η)) (one_lt_two : (1 : ℝ) < 2)
  obtain ⟨k, hkK, hkgt⟩ := hKinf.exists_gt (max k1 n1)
  have hk1k : k1 ≤ k := (le_max_left _ _).trans hkgt.le
  have hn1k : n1 ≤ k := (le_max_right _ _).trans hkgt.le
  have hs2 : 2 ≤ (2 : ℝ) ^ k := by
    have h1 : (2 : ℝ) ^ n1 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hn1k
    exact (le_max_left _ _).trans (hn1.le.trans h1)
  have hstep : |G0| + |(dl + dr) / 2| + M0 ≤ η * (2 : ℝ) ^ k / 2 := by
    have h1 : (2 : ℝ) ^ n1 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hn1k
    have h2 : 2 * (|G0| + |(dl + dr) / 2| + M0) / η ≤ (2 : ℝ) ^ k :=
      (le_max_right _ _).trans (hn1.le.trans h1)
    rw [div_le_iff₀ hη0] at h2
    nlinarith
  have hK : 3 * η * (2 : ℝ) ^ k + |(dl + dr) / 2| * (2 * (2 : ℝ) ^ k + 2) <
      100 * (1 + |dl| + |dr|) * (2 : ℝ) ^ k :=
    rare_K_of_one_le dl dr η _ hη1 (by linarith)
  -- `m := nk k ≥ 1`.
  have hnk1 : 1 ≤ nk k := by
    have h := (hnk k (hKset' k hkK)).1
    have hpow : (1 : ℝ) ≤ 2 ^ m k := one_le_pow₀ (by norm_num)
    have : (0 : ℝ) < nk k := by linarith
    exact_mod_cast this
  exact corner_excluded_at_scale μ hneg hpos M0 hbup g hgcont hghom hgconc hgshape a ha₀ ha₁ H hH
    dl dr c η G0 hdl hdr hc hcpos hη hG0 ((2 : ℝ) ^ k) hs2 (nk k) hnk1
    (100 * (1 + |dl| + |dr|)) q0 hq0₀ hsmall hK hstep (hk1 k hkK hk1k)

/-- **Theorem 2.1 of the differentiability preprint for bounded weights when no direction lies on
the flat segment.**
If every direction `(a, 1 - a)` has top-weight shape below `1`, the quadrant extension of `g`
is differentiable at every point of the open quadrant, by homogeneity. -/
theorem differentiableAt_of_bounded_no_flat
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (M : ℝ) (hb : ∀ᵐ x ∂μ, |x| ≤ M)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (hoff : ∀ a : ℝ, 0 < a → a < 1 → ∃ Gtop : ℝ,
      Tendsto (fun m : ℕ => (∫ ω : Environment, lastPassage (fun z =>
        if (ω z : EReal) = sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then (1 : ℝ) else 0)
          0 (⌊(m : ℝ) * a⌋₊, ⌊(m : ℝ) * (1 - a)⌋₊) ∂environmentLaw μ) / (m : ℝ))
        atTop (𝓝 Gtop) ∧ Gtop < 1) :
    ∀ x : ℝ × ℝ, 0 < x.1 → 0 < x.2 → DifferentiableAt ℝ (quadrantExtension g) x :=
  differentiableAt_quadrantExtension_of_segment g hghom fun a ha₀ ha₁ => by
    obtain ⟨Gtop, htop, hgap⟩ := hoff a ha₀ ha₁
    exact differentiableAt_of_bounded_off_flat μ M hb g hgcont hghom hgconc hgshape a ha₀ ha₁
      Gtop htop hgap

end LPPDifferentiability
