/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.FirstPassage
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Growth sets from passage times for one environment

This file follows Martin (2004), Section 5.3. The inclusions (5.3) follow once
`|T z - g z| < ε ‖z‖` for all but finitely many lattice points `z`. Martin states this
deterministic step without proof; here it is written out. Two points are passed over in
Martin's argument: the floors in `B(t) = {x | T ⌊x⌋ ≤ t}` (handled by continuity and
homogeneity of `g`),
and the small points near the origin (handled by finiteness). This is why the conclusion
holds only for large `t`.

The size `‖x‖` is `x.1 + x.2`.
-/

@[expose] public section

open Set
open scoped NNReal Pointwise

namespace LPPDifferentiability

/-- The part of the quadrant of size at most `R` is compact: it is closed and bounded in a proper
space. Used for the bounds on `g` near the origin and for the uniform continuity of `g`. -/
private theorem isCompact_size_le (R : ℝ≥0) :
    IsCompact {x : Quadrant | x.1 + x.2 ≤ R} := by
  have hclosed : IsClosed {x : Quadrant | x.1 + x.2 ≤ R} :=
    isClosed_le (continuous_fst.add continuous_snd) continuous_const
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  refine (Metric.isBounded_closedBall (x := ((0 : ℝ≥0), (0 : ℝ≥0))) (r := (R : ℝ))).subset ?_
  intro x hx
  have hcoord : ∀ a : ℝ≥0, a ≤ R → dist a (0 : ℝ≥0) ≤ (R : ℝ) := by
    intro a ha
    rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg a)]
    exact NNReal.coe_le_coe.mpr ha
  rw [Metric.mem_closedBall, Prod.dist_eq]
  exact max_le (hcoord _ (le_trans le_self_add hx)) (hcoord _ (le_trans le_add_self hx))

/-- A continuous function on the quadrant is bounded above on the points of size at most `R`.
This is the bound on `g` near the origin. -/
private theorem exists_short_bound {g : Quadrant → ℝ} (hcont : Continuous g) (R : ℝ≥0) :
    ∃ M : ℝ, ∀ y : Quadrant, y.1 + y.2 ≤ R → g y ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_size_le R).bddAbove_image hcont.continuousOn
  exact ⟨M, fun y hy => hM ⟨y, hy, rfl⟩⟩

/-- Any real function of lattice points is bounded above on the finitely many lattice points whose
coordinates sum to at most `n`. This is the bound on `T` near the origin. -/
private theorem exists_short_time_bound (T : ℕ × ℕ → ℝ) (n : ℕ) :
    ∃ M : ℝ, ∀ z : ℕ × ℕ, z.1 + z.2 ≤ n → T z ≤ M := by
  refine ⟨∑ w ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1), |T w|, ?_⟩
  intro z hz
  have hmem : z ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) := by
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  exact (le_abs_self _).trans
    (Finset.single_le_sum (f := fun w => |T w|) (fun w _ => abs_nonneg _) hmem)

/-- The floor of a point of the quadrant moves each coordinate down by less than 1. -/
private theorem floor_coord_bounds (a : ℝ≥0) :
    ((⌊a⌋₊ : ℕ) : ℝ) ≤ (a : ℝ) ∧ (a : ℝ) < ((⌊a⌋₊ : ℕ) : ℝ) + 1 := by
  constructor
  · have := Nat.floor_le (a := a) (by positivity)
    exact_mod_cast this
  · have := Nat.lt_floor_add_one a
    exact_mod_cast this

/-- The floors do not change `g` much, relative to the size.
For a continuous, positively homogeneous `g` and any `η > 0` there is a natural number `R` such
that `|g y - g (⌊y.1⌋₊, ⌊y.2⌋₊)| ≤ η (y.1 + y.2)` for all `y` with `y.1 + y.2 ≥ R`.
Proof: scale `y` to size 1, where `g` is uniformly continuous on a compact set; the floor moves
the scaled point by at most `1 / (y.1 + y.2)`. -/
private theorem exists_floor_error {g : Quadrant → ℝ} (hcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    {η : ℝ} (hη : 0 < η) :
    ∃ R : ℕ, ∀ y : Quadrant, (R : ℝ) ≤ (y.1 : ℝ) + y.2 →
      |g y - g ((⌊y.1⌋₊ : ℝ≥0), (⌊y.2⌋₊ : ℝ≥0))| ≤ η * ((y.1 : ℝ) + y.2) := by
  have huc := (isCompact_size_le 1).uniformContinuousOn_of_continuous hcont.continuousOn
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.mp huc η hη
  refine ⟨⌈2 / δ⌉₊, fun y hy => ?_⟩
  have hy' : 2 / δ ≤ (y.1 : ℝ) + y.2 := le_trans (Nat.le_ceil _) hy
  obtain ⟨hf1, hf1'⟩ := floor_coord_bounds y.1
  obtain ⟨hf2, hf2'⟩ := floor_coord_bounds y.2
  have hNpos : 0 < (y.1 : ℝ) + y.2 := lt_of_lt_of_le (by positivity) hy'
  -- the scale s = 1 / (y.1 + y.2), so that s * (y.1 + y.2) = 1
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, (s : ℝ) * ((y.1 : ℝ) + y.2) = 1 := by
    refine ⟨((y.1 + y.2 : ℝ≥0))⁻¹, ?_⟩
    rw [NNReal.coe_inv, NNReal.coe_add]
    exact inv_mul_cancel₀ hNpos.ne'
  have hs0 : (0 : ℝ) ≤ s := s.2
  have hsδ : (s : ℝ) < δ := by
    have h1 : 2 ≤ ((y.1 : ℝ) + y.2) * δ := by
      have := mul_le_mul_of_nonneg_right hy' hδ.le
      rwa [div_mul_cancel₀ _ hδ.ne'] at this
    have h2 : (s : ℝ) * 2 ≤ (s : ℝ) * (((y.1 : ℝ) + y.2) * δ) :=
      mul_le_mul_of_nonneg_left h1 hs0
    have h3 : (s : ℝ) * (((y.1 : ℝ) + y.2) * δ) = δ := by
      calc (s : ℝ) * (((y.1 : ℝ) + y.2) * δ) = ((s : ℝ) * ((y.1 : ℝ) + y.2)) * δ := by ring
        _ = δ := by rw [hs, one_mul]
    linarith
  -- the scaled point and the scaled floor point lie in the compact set of size at most 1
  have hmem1 : ((s * y.1, s * y.2) : Quadrant) ∈ {x : Quadrant | x.1 + x.2 ≤ 1} := by
    show s * y.1 + s * y.2 ≤ 1
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith
  have hmem2 : ((s * (⌊y.1⌋₊ : ℝ≥0), s * (⌊y.2⌋₊ : ℝ≥0)) : Quadrant) ∈
      {x : Quadrant | x.1 + x.2 ≤ 1} := by
    show s * (⌊y.1⌋₊ : ℝ≥0) + s * (⌊y.2⌋₊ : ℝ≥0) ≤ 1
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hf1 hf2) hs0]
  have hcoord : ∀ (a : ℝ≥0) (f : ℕ), ((f : ℕ) : ℝ) ≤ (a : ℝ) → (a : ℝ) < (f : ℝ) + 1 →
      dist (s * a) (s * (f : ℝ≥0)) < δ := by
    intro a f h1 h2
    rw [NNReal.dist_eq]
    push_cast
    have h4 : (s : ℝ) * a - s * f ≤ s := by nlinarith [mul_le_mul_of_nonneg_left h2.le hs0]
    have h5 : -(s : ℝ) ≤ (s : ℝ) * a - s * f := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hs0]
    exact lt_of_le_of_lt (abs_le.mpr ⟨h5, h4⟩) hsδ
  have hdist : dist ((s * y.1, s * y.2) : Quadrant)
      ((s * (⌊y.1⌋₊ : ℝ≥0), s * (⌊y.2⌋₊ : ℝ≥0)) : Quadrant) < δ := by
    rw [Prod.dist_eq]
    exact max_lt (hcoord _ _ hf1 hf1') (hcoord _ _ hf2 hf2')
  have hclose := hδ' _ hmem1 _ hmem2 hdist
  have hga : g (s * y.1, s * y.2) = (s : ℝ) * g y := hhom s y
  have hgb : g (s * (⌊y.1⌋₊ : ℝ≥0), s * (⌊y.2⌋₊ : ℝ≥0)) =
      (s : ℝ) * g ((⌊y.1⌋₊ : ℝ≥0), (⌊y.2⌋₊ : ℝ≥0)) :=
    hhom s ((⌊y.1⌋₊ : ℝ≥0), (⌊y.2⌋₊ : ℝ≥0))
  rw [Real.dist_eq, hga, hgb] at hclose
  -- undo the scaling: g y - g fl = (y.1 + y.2) * (s * g y - s * g fl)
  have hunscale : g y - g ((⌊y.1⌋₊ : ℝ≥0), (⌊y.2⌋₊ : ℝ≥0)) =
      ((y.1 : ℝ) + y.2) * ((s : ℝ) * g y - (s : ℝ) * g ((⌊y.1⌋₊ : ℝ≥0), (⌊y.2⌋₊ : ℝ≥0))) := by
    linear_combination (-(g y - g ((⌊y.1⌋₊ : ℝ≥0), (⌊y.2⌋₊ : ℝ≥0)))) * hs
  rw [hunscale, abs_mul, abs_of_pos hNpos]
  nlinarith [mul_le_mul_of_nonneg_left hclose.le hNpos.le]

/-- If `ε ≤ 1` is not assumed, the truncated scalar `1 - ε` still satisfies
`(1 - ε)(1 + θ) ≤ 1` whenever `θ ≤ ε`. The lower inclusion
needs a relative error `θ` that is at most `ε`. -/
private theorem coe_one_sub_mul_le (ε : ℝ≥0) {θ : ℝ} (hθ : θ ≤ ε) :
    ((1 - ε : ℝ≥0) : ℝ) * (1 + θ) ≤ 1 := by
  rcases le_total ε 1 with hle | hle
  · have h1 : ((1 - ε : ℝ≥0) : ℝ) = 1 - ε := by rw [NNReal.coe_sub hle, NNReal.coe_one]
    have h0 : 0 ≤ (1 : ℝ) - ε := by rw [← h1]; exact NNReal.coe_nonneg _
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add_right hθ 1) h0, sq_nonneg (ε : ℝ)]
  · rw [tsub_eq_zero_of_le hle]
    simp

/-- Upper growth-set inclusion for one fixed environment (deterministic form of the right
inclusion in (5.3) of Martin (2004)). If `g` is continuous, positively homogeneous and at least
`c ‖x‖` for some `c > 0`, and `T z` is within `ε ‖z‖` of `g z` for all long `z`, then for every
`ε > 0` and all large `t`, the rescaled growth set `t⁻¹ • {x | T ⌊x⌋ ≤ t}` lies inside
`(1 + ε) • {x | g x ≤ 1}`. Source: Martin (2004), Section 5.3. -/
theorem growth_set_upper_inclusion (T : ℕ × ℕ → ℝ) (g : Quadrant → ℝ)
    (hcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ x : Quadrant, c * ((x.1 : ℝ) + x.2) ≤ g x)
    (hT : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
      |T z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤ ε * ((z.1 + z.2 : ℕ) : ℝ)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t →
      t⁻¹ • {x : Quadrant | T (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ⊆
        (1 + ε) • {x : Quadrant | g x ≤ 1} := by
  intro ε hε
  obtain ⟨c, hc, hlow⟩ := hlow
  have he : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
  -- the relative error θ = ε / (1 + ε), shared equally by the times and the floors: κ = c θ / 2
  obtain ⟨θ, hθ0, hθe⟩ : ∃ θ : ℝ, 0 < θ ∧ θ * (1 + ε) = ε :=
    ⟨ε / (1 + ε), by positivity, by field_simp⟩
  obtain ⟨κ, hκ, hκθ⟩ : ∃ κ : ℝ, 0 < κ ∧ κ * 2 = c * θ :=
    ⟨c * θ / 2, by positivity, by ring⟩
  obtain ⟨N, hN⟩ := hT κ hκ
  obtain ⟨R, hR⟩ := exists_floor_error hcont hhom hκ
  -- m: the size beyond which the floor point is long and the floor error is controlled
  obtain ⟨m, hmR, hmN⟩ : ∃ m : ℕ, R ≤ m ∧ N + 2 ≤ m :=
    ⟨max R (N + 2), le_max_left _ _, le_max_right _ _⟩
  have hmR' : (R : ℝ) ≤ m := by exact_mod_cast hmR
  have hmN' : (N : ℝ) + 2 ≤ m := by exact_mod_cast hmN
  obtain ⟨M, hM⟩ := exists_short_bound hcont (m : ℝ≥0)
  refine ⟨max (Real.toNNReal M) 1, fun t ht => ?_⟩
  have hMt : M ≤ (t : ℝ) := Real.toNNReal_le_iff_le_coe.mp (le_trans (le_max_left _ _) ht)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast le_trans (le_max_right _ _) ht
  have ht0 : (0 : ℝ) < t := by linarith
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
  have hTy : T (⌊y.1⌋₊, ⌊y.2⌋₊) ≤ (t : ℝ) := hy
  -- core: the point y satisfies g y ≤ (1 + ε) t
  have hgy : g y ≤ (1 + ε) * t := by
    by_cases hlong : (m : ℝ) ≤ (y.1 : ℝ) + y.2
    · obtain ⟨hf1, hf1'⟩ := floor_coord_bounds y.1
      obtain ⟨hf2, hf2'⟩ := floor_coord_bounds y.2
      have hzN : N < ⌊y.1⌋₊ + ⌊y.2⌋₊ := by
        have : (N : ℝ) < ((⌊y.1⌋₊ + ⌊y.2⌋₊ : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      have hTz := hN (⌊y.1⌋₊, ⌊y.2⌋₊) (le_of_lt hzN)
      dsimp only at hTz
      have hTz' := abs_le.mp hTz
      have hcast : ((⌊y.1⌋₊ + ⌊y.2⌋₊ : ℕ) : ℝ) ≤ (y.1 : ℝ) + y.2 := by push_cast; linarith
      have hfl := abs_le.mp (hR y (le_trans hmR' hlong))
      have hcy := hlow y
      have hA := mul_le_mul_of_nonneg_left hcast hκ.le
      have hB := mul_le_mul_of_nonneg_left hcy hθ0.le
      have hC : κ * 2 * ((y.1 : ℝ) + y.2) = c * θ * ((y.1 : ℝ) + y.2) := by rw [hκθ]
      -- (1 - θ) g y ≤ t
      have hsmall : g y - θ * g y ≤ t := by nlinarith [hTz'.1, hfl.2, hA, hB, hC, hTy]
      calc g y = (1 + ε) * (g y - θ * g y) := by linear_combination (g y) * hθe
        _ ≤ (1 + ε) * t := mul_le_mul_of_nonneg_left hsmall (by positivity)
    · have hshort : y.1 + y.2 ≤ (m : ℝ≥0) := by
        rw [← NNReal.coe_le_coe]
        push_cast
        linarith [not_le.mp hlong]
      have h1 := hM y hshort
      nlinarith [mul_pos he ht0]
  -- write t⁻¹ • y as (1 + ε) • b with b = ((1 + ε) t)⁻¹ • y, which lies in the set g ≤ 1
  have h1ε : (1 + ε : ℝ≥0) ≠ 0 := by positivity
  refine Set.mem_smul_set.mpr ⟨((1 + ε) * t)⁻¹ • y, ?_, ?_⟩
  · show g (((1 + ε) * t)⁻¹ * y.1, ((1 + ε) * t)⁻¹ * y.2) ≤ 1
    rw [hhom, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one]
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  · rw [smul_smul, mul_inv, mul_inv_cancel_left₀ h1ε]

/-- Lower growth-set inclusion for one fixed environment (deterministic form of the left inclusion
in (5.3) of Martin (2004)), under the same hypotheses as `growth_set_upper_inclusion`: for every
`ε > 0` and all large `t`, `(1 - ε) • {x | g x ≤ 1}` lies inside `t⁻¹ • {x | T ⌊x⌋ ≤ t}`.
The scalar `1 - ε` is computed in `ℝ≥0`, so it is truncated at zero.
Source: Martin (2004), Section 5.3. -/
theorem growth_set_lower_inclusion (T : ℕ × ℕ → ℝ) (g : Quadrant → ℝ)
    (hcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ x : Quadrant, c * ((x.1 : ℝ) + x.2) ≤ g x)
    (hT : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
      |T z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤ ε * ((z.1 + z.2 : ℕ) : ℝ)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t →
      (1 - ε) • {x : Quadrant | g x ≤ 1} ⊆
        t⁻¹ • {x : Quadrant | T (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} := by
  intro ε hε
  obtain ⟨c, hc, hlow⟩ := hlow
  have he : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
  -- the relative error θ = ε / (1 + ε) ≤ ε, shared equally by the times and the floors
  obtain ⟨θ, hθ0, hθε⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ ε :=
    ⟨ε / (1 + ε), by positivity, by rw [div_le_iff₀ (by positivity)]; nlinarith⟩
  obtain ⟨κ, hκ, hκθ⟩ : ∃ κ : ℝ, 0 < κ ∧ κ * 2 = c * θ :=
    ⟨c * θ / 2, by positivity, by ring⟩
  obtain ⟨N, hN⟩ := hT κ hκ
  obtain ⟨R, hR⟩ := exists_floor_error hcont hhom hκ
  obtain ⟨m, hmR, hmN⟩ : ∃ m : ℕ, R ≤ m ∧ N + 2 ≤ m :=
    ⟨max R (N + 2), le_max_left _ _, le_max_right _ _⟩
  have hmR' : (R : ℝ) ≤ m := by exact_mod_cast hmR
  have hmN' : (N : ℝ) + 2 ≤ m := by exact_mod_cast hmN
  obtain ⟨M, hM⟩ := exists_short_time_bound T m
  refine ⟨max (Real.toNNReal M) 1, fun t ht => ?_⟩
  have hMt : M ≤ (t : ℝ) := Real.toNNReal_le_iff_le_coe.mp (le_trans (le_max_left _ _) ht)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast le_trans (le_max_right _ _) ht
  have ht0 : (0 : ℝ) < t := by linarith
  have htne : t ≠ 0 := (NNReal.coe_pos.mp ht0).ne'
  intro x hx
  obtain ⟨b, hb, rfl⟩ := Set.mem_smul_set.mp hx
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero htne), inv_inv]
  -- the point y = t • (1 - ε) • b has g y ≤ t (1 - ε)
  obtain ⟨y, hyy⟩ : ∃ y : Quadrant, y = t • (1 - ε) • b := ⟨_, rfl⟩
  have hb1 : g b ≤ 1 := hb
  have hgy : g y ≤ (t : ℝ) * ((1 - ε : ℝ≥0) : ℝ) := by
    have h1 : g (t • (1 - ε) • b) = (t : ℝ) * g ((1 - ε) • b) := hhom t ((1 - ε) • b)
    have h2 : g ((1 - ε) • b) = ((1 - ε : ℝ≥0) : ℝ) * g b := hhom (1 - ε) b
    rw [hyy, h1, h2]
    have h3 : (0 : ℝ) ≤ (t : ℝ) * ((1 - ε : ℝ≥0) : ℝ) := mul_nonneg t.2 (NNReal.coe_nonneg _)
    nlinarith
  rw [← hyy]
  show T (⌊y.1⌋₊, ⌊y.2⌋₊) ≤ (t : ℝ)
  by_cases hlong : (m : ℝ) ≤ (y.1 : ℝ) + y.2
  · obtain ⟨hf1, hf1'⟩ := floor_coord_bounds y.1
    obtain ⟨hf2, hf2'⟩ := floor_coord_bounds y.2
    have hzN : N < ⌊y.1⌋₊ + ⌊y.2⌋₊ := by
      have : (N : ℝ) < ((⌊y.1⌋₊ + ⌊y.2⌋₊ : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hTz := hN (⌊y.1⌋₊, ⌊y.2⌋₊) (le_of_lt hzN)
    dsimp only at hTz
    have hTz' := abs_le.mp hTz
    have hcast : ((⌊y.1⌋₊ + ⌊y.2⌋₊ : ℕ) : ℝ) ≤ (y.1 : ℝ) + y.2 := by push_cast; linarith
    have hfl := abs_le.mp (hR y (le_trans hmR' hlong))
    have hcy := hlow y
    have hA := mul_le_mul_of_nonneg_left hcast hκ.le
    have hB := mul_le_mul_of_nonneg_left hcy hθ0.le
    have hC : κ * 2 * ((y.1 : ℝ) + y.2) = c * θ * ((y.1 : ℝ) + y.2) := by rw [hκθ]
    -- T z ≤ (1 + θ) g y
    have hsmall : T (⌊y.1⌋₊, ⌊y.2⌋₊) ≤ (1 + θ) * g y := by
      nlinarith [hTz'.2, hfl.1, hA, hB, hC]
    have hfinal : (1 + θ) * g y ≤ (1 + θ) * ((t : ℝ) * ((1 - ε : ℝ≥0) : ℝ)) :=
      mul_le_mul_of_nonneg_left hgy (by positivity)
    have hkey := coe_one_sub_mul_le ε hθε
    have hkey' := mul_le_mul_of_nonneg_left hkey ht0.le
    nlinarith [hsmall, hfinal, hkey']
  · have hfsum : ⌊y.1⌋₊ + ⌊y.2⌋₊ ≤ m := by
      obtain ⟨hf1, _⟩ := floor_coord_bounds y.1
      obtain ⟨hf2, _⟩ := floor_coord_bounds y.2
      have : ((⌊y.1⌋₊ + ⌊y.2⌋₊ : ℕ) : ℝ) ≤ m := by
        push_cast
        linarith [not_le.mp hlong]
      exact_mod_cast this
    exact le_trans (hM (⌊y.1⌋₊, ⌊y.2⌋₊) hfsum) hMt

/-- Growth-set inclusions for one fixed environment (deterministic reduction behind Martin's
Theorem 5.1). Under the hypotheses of `growth_set_upper_inclusion`, for every `ε > 0` and all large
`t`, `(1 - ε) • {x | g x ≤ 1} ⊆ t⁻¹ • {x | T ⌊x⌋ ≤ t} ⊆ (1 + ε) • {x | g x ≤ 1}`. This is the
form used by the last-passage and first-passage statements below, for one environment.
Source: Martin (2004), Section 5.3. -/
theorem growth_set_inclusions (T : ℕ × ℕ → ℝ) (g : Quadrant → ℝ)
    (hcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ x : Quadrant, c * ((x.1 : ℝ) + x.2) ≤ g x)
    (hT : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
      |T z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤ ε * ((z.1 + z.2 : ℕ) : ℝ)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t →
      (1 - ε) • {x : Quadrant | g x ≤ 1} ⊆
          t⁻¹ • {x : Quadrant | T (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ∧
        t⁻¹ • {x : Quadrant | T (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ⊆
          (1 + ε) • {x : Quadrant | g x ≤ 1} := by
  intro ε hε
  obtain ⟨t₁, h₁⟩ := growth_set_lower_inclusion T g hcont hhom hlow hT ε hε
  obtain ⟨t₂, h₂⟩ := growth_set_upper_inclusion T g hcont hhom hlow hT ε hε
  exact ⟨max t₁ t₂, fun t ht =>
    ⟨h₁ t (le_trans (le_max_left _ _) ht), h₂ t (le_trans (le_max_right _ _) ht)⟩⟩

/-- Last-passage growth-set inclusions for one fixed environment `ω` (Martin's Theorem 5.1(i),
after the reduction of Section 5.3). If `g` is continuous, positively homogeneous,
at least `c ‖x‖`, and
`lastPassage ω (0, 0) z` is within `ε ‖z‖` of `g z` for all long `z`, then for every `ε > 0` and
all large `t`, `(1 - ε) B ⊆ B(t)/t ⊆ (1 + ε) B` with
`B(t) = {x | lastPassage ω 0 ⌊x⌋ ≤ t}` and `B = {x | g x ≤ 1}`. This is the deterministic
step in the proof of Martin's Theorem 5.1(i). Source: Martin (2004), Section 5.3. -/
theorem lastPassage_growth_set_inclusions (ω : Environment) (g : Quadrant → ℝ)
    (hcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ x : Quadrant, c * ((x.1 : ℝ) + x.2) ≤ g x)
    (hT : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
      |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
        ε * ((z.1 + z.2 : ℕ) : ℝ)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t →
      (1 - ε) • {x : Quadrant | g x ≤ 1} ⊆
          t⁻¹ • {x : Quadrant | lastPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ∧
        t⁻¹ • {x : Quadrant | lastPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ⊆
          (1 + ε) • {x : Quadrant | g x ≤ 1} :=
  growth_set_inclusions (fun z => lastPassage ω 0 z) g hcont hhom hlow hT

/-- First-passage growth-set inclusions for one fixed environment `ω` (Martin's Theorem 5.1(ii),
after the reduction of Section 5.3). If `h` is continuous, positively homogeneous,
at least `c ‖x‖`, and
`firstPassage ω (0, 0) z` is within `ε ‖z‖` of `h z` for all long `z`, then for every `ε > 0` and
all large `t`, `(1 - ε) C ⊆ C(t)/t ⊆ (1 + ε) C` with `C(t) = {x | firstPassage ω 0 ⌊x⌋ ≤ t}` and
`C = {x | h x ≤ 1}`. This is the deterministic step in the proof of Martin's Theorem 5.1(ii). The
proof is the same as for the last-passage case, since the reduction uses no property of the passage
function other than the closeness to the shape function. Source: Martin (2004), Section 5.3. -/
theorem firstPassage_growth_set_inclusions (ω : Environment) (h : Quadrant → ℝ)
    (hcont : Continuous h)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), h (c * x.1, c * x.2) = (c : ℝ) * h x)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ x : Quadrant, c * ((x.1 : ℝ) + x.2) ≤ h x)
    (hT : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
      |firstPassage ω (0, 0) z - h ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
        ε * ((z.1 + z.2 : ℕ) : ℝ)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t →
      (1 - ε) • {x : Quadrant | h x ≤ 1} ⊆
          t⁻¹ • {x : Quadrant | firstPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ∧
        t⁻¹ • {x : Quadrant | firstPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ⊆
          (1 + ε) • {x : Quadrant | h x ≤ 1} :=
  growth_set_inclusions (fun z => firstPassage ω 0 z) h hcont hhom hlow hT

end LPPDifferentiability
