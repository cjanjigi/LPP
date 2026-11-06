/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.Travel
public import Differentiability.Model.Paths.TransverseStaircase
import LPP_Foundations.Analysis.HomogeneousShapeLipschitz
import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.Probability.CDF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Short-length abundance of crossings

For every `C`, crossings of a strip of width of order `s` and length `n ≤ C s` that beat `g(ξ) n` by
at most `K s` occur with probability tending to one, uniformly in `1 ≤ n ≤ C s` ((4.4) of the
differentiability preprint, in Proposition 4.3). Large `n` use the travel lemma at scale `n`; the
finitely many small `n` use the deterministic staircase.

## References

* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace LPPDifferentiability

/-- The travel conclusion of `exists_unique_shape_with_travel`, for one shape. -/
private def TravelFor (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) : Prop :=
  ∀ (a : ℝ), 0 < a → a < 1 → ∀ (D : ℝ), 1 ≤ D →
    ∀ (theta : ℝ), 0 < theta → theta < min a (1 - a) →
    ∀ (η δ : ℝ), 0 < η → 0 < δ →
    ∃ s1 : ℝ, 1 ≤ s1 ∧ ∃ p : ℝ → ℝ,
      (∀ s, 0 ≤ p s ∧ p s ≤ 1) ∧ Tendsto p atTop (𝓝 1) ∧
      ∀ (s : ℝ) (u : Lattice) (d : ℕ × ℕ), s1 ≤ s →
        s ≤ ((d.1 + d.2 : ℕ) : ℝ) → ((d.1 + d.2 : ℕ) : ℝ) ≤ D * s →
        |(1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)| ≤
          (min a (1 - a) - theta) * ((d.1 : ℝ) + (d.2 : ℝ)) →
        MeasurableSet {ω : Environment | ∃ q : Path u d,
          g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) - η * s ≤ pathWeight ω q ∧
          ∀ i, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
            |((q.vertex i).1 : ℝ) - ((u.1 : ℝ) + t * (d.1 : ℝ))| +
              |((q.vertex i).2 : ℝ) - ((u.2 : ℝ) + t * (d.2 : ℝ))| ≤ δ * s} ∧
        p s ≤ (environmentLaw μ).real {ω : Environment | ∃ q : Path u d,
          g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) - η * s ≤ pathWeight ω q ∧
          ∀ i, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
            |((q.vertex i).1 : ℝ) - ((u.1 : ℝ) + t * (d.1 : ℝ))| +
              |((q.vertex i).2 : ℝ) - ((u.2 : ℝ) + t * (d.2 : ℝ))| ≤ δ * s}

/-- The crossing event, spelled as in the statement of the main theorem. -/
private def crossing (a G0 K s : ℝ) (n : ℕ) : Set Environment :=
  {ω : Environment | ∃ q : Σ i : Fin (n + 1), Path (0 : Lattice) (i.val, n - i.val),
    (∀ j, |(1 - a) * ((q.2.vertex j).1 : ℝ) - a * ((q.2.vertex j).2 : ℝ)| ≤ 8 * s) ∧
      G0 * (n : ℝ) - K * s < pathWeight ω q.2}

/-- A fixed measurable real variable is above a threshold tending to `-∞` with
probability tending to one. -/
private theorem eventually_lt_measureReal_gt {P : Measure Environment}
    [IsProbabilityMeasure P] (S : Environment → ℝ) (hS : Measurable S) (t : ℝ → ℝ)
    (ht : Tendsto t atTop atBot) (c : ℝ) (hc : c < 1) :
    ∀ᶠ s in atTop, c < P.real {ω | t s < S ω} := by
  have : IsProbabilityMeasure (P.map S) :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).2 inferInstance
  have h1 : Tendsto (fun s => P.real {ω | S ω ≤ t s}) atTop (𝓝 0) := by
    refine ((ProbabilityTheory.tendsto_cdf_atBot (P.map S)).comp ht).congr (fun s => ?_)
    simp only [Function.comp, ProbabilityTheory.cdf_eq_real]
    rw [map_measureReal_apply hS measurableSet_Iic]
    rfl
  filter_upwards [h1.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < 1 - c))] with s hs
  have hm : MeasurableSet {ω | S ω ≤ t s} := hS measurableSet_Iic
  have hcompl : {ω | t s < S ω} = {ω | S ω ≤ t s}ᶜ := by
    ext ω
    simp
  have hsum := measureReal_add_measureReal_compl (μ := P) hm
  rw [hcompl]
  simp only [probReal_univ] at hsum
  linarith

/-- For a fixed length `n`, the staircase gives a crossing with probability
tending to one as `s → ∞`. -/
private theorem small_length_crossing (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a G0 K : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hK : 0 < K) (n : ℕ) (c : ℝ) (hc : c < 1) :
    ∀ᶠ s in atTop, c < (environmentLaw μ).real (crossing a G0 K s n) := by
  obtain ⟨i, q, hq⟩ := exists_origin_staircase a ha₀ ha₁ n
  have hlin : Tendsto (fun s : ℝ => K * s) atTop atTop :=
    tendsto_id.const_mul_atTop hK
  have ht : Tendsto (fun s : ℝ => G0 * (n : ℝ) - K * s) atTop atBot := by
    refine (tendsto_atBot_add_const_left atTop (G0 * (n : ℝ))
      (tendsto_neg_atTop_atBot.comp hlin)).congr (fun s => ?_)
    simp [sub_eq_add_neg]
  filter_upwards [eventually_lt_measureReal_gt (P := environmentLaw μ)
    (fun ω => pathWeight ω q) (measurable_pathWeight q) _ ht c hc,
    eventually_ge_atTop (1 : ℝ)] with s hs hs1
  refine hs.trans_le (measureReal_mono ?_)
  intro ω hω
  exact ⟨⟨i, q⟩, fun j => ((hq j).le.trans (by linarith)), hω⟩

/-- Two lattice-point facts about the point on level `n` with transverse
coordinate in `(-1, 0]`. -/
private theorem floor_point_facts (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (n : ℕ) :
    ⌊a * (n : ℝ)⌋₊ ≤ n ∧ (⌊a * (n : ℝ)⌋₊ : ℝ) ≤ a * n ∧ a * n < ⌊a * (n : ℝ)⌋₊ + 1 := by
  have hn : (0 : ℝ) ≤ a * n := by positivity
  refine ⟨?_, Nat.floor_le hn, Nat.lt_floor_add_one _⟩
  apply Nat.floor_le_of_le
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]


/-- On level `n`, the point `(j, n - j)` has transverse coordinate `j - a n`. -/
private theorem floor_point_transverse (a : ℝ) (n j : ℕ) (hj : j ≤ n) :
    (1 - a) * (j : ℝ) - a * ((n - j : ℕ) : ℝ) = (j : ℝ) - a * n := by
  rw [Nat.cast_sub hj]
  ring

/-- A vertex within `B` (in the real l1 distance) of the point `t d`, where the transverse
coordinate of `d` is at most one, has transverse coordinate at most `B + 1` ((2.8) of the
differentiability preprint and `|r| ≤ 1` on the segment). -/
private theorem transverse_tube_bound (a t v₁ v₂ d₁ d₂ B s : ℝ) (ha₀ : 0 < a)
    (ha₁ : a < 1) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hd : |(1 - a) * d₁ - a * d₂| ≤ 1)
    (hdev : |v₁ - (0 + t * d₁)| + |v₂ - (0 + t * d₂)| ≤ B) (hB : B ≤ 4 * s)
    (hs : 1 ≤ s) : |(1 - a) * v₁ - a * v₂| ≤ 8 * s := by
  have hsplit : (1 - a) * v₁ - a * v₂ =
      ((1 - a) * (v₁ - (0 + t * d₁)) - a * (v₂ - (0 + t * d₂))) +
        t * ((1 - a) * d₁ - a * d₂) := by ring
  have hA : |(1 - a) * (v₁ - (0 + t * d₁)) - a * (v₂ - (0 + t * d₂))| ≤
      |v₁ - (0 + t * d₁)| + |v₂ - (0 + t * d₂)| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos (sub_pos.2 ha₁), abs_of_pos ha₀]
    have h1 := mul_nonneg ha₀.le (abs_nonneg (v₁ - (0 + t * d₁)))
    have h2 := mul_nonneg (sub_pos.2 ha₁).le (abs_nonneg (v₂ - (0 + t * d₂)))
    linarith
  have hC : |t * ((1 - a) * d₁ - a * d₂)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg ht₀]
    calc t * |(1 - a) * d₁ - a * d₂| ≤ 1 * 1 :=
          mul_le_mul ht₁ hd (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [hsplit]
  calc _ ≤ |(1 - a) * (v₁ - (0 + t * d₁)) - a * (v₂ - (0 + t * d₂))| +
        |t * ((1 - a) * d₁ - a * d₂)| := abs_add_le _ _
    _ ≤ 8 * s := by linarith

/-- The weight bound of step 3 of the proof of Proposition 4.3 of the differentiability preprint,
with `η = K / (2 C)`. -/
private theorem weight_strict (K C s L G0 gd W nn : ℝ) (hK : 0 < K) (hC : 0 < C)
    (hns : nn ≤ C * s) (hsL : 4 * L / K < s) (hshape : nn * G0 - 2 * L ≤ gd)
    (hW : gd - K / (2 * C) * nn ≤ W) : G0 * nn - K * s < W := by
  have hη : K / (2 * C) * nn ≤ K * s / 2 := by
    calc K / (2 * C) * nn ≤ K / (2 * C) * (C * s) :=
          mul_le_mul_of_nonneg_left hns (by positivity)
      _ = K * s / 2 := by
          rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]
          ring
  have hLK : 2 * L < K * s / 2 := by
    have := (div_lt_iff₀ hK).1 hsL
    linarith
  linarith [mul_comm G0 nn]

/-- Step 3 of the proof of Proposition 4.3 of the differentiability preprint: the travel event at
scale `n` forces a crossing, once `n ≤ C s`, `s ≥ 1` and `s > 4 L / K`. -/
private theorem travel_subset (a K C s L G0 gd : ℝ) (n j : ℕ) (ha₀ : 0 < a)
    (ha₁ : a < 1) (hK : 0 < K) (hC : 0 < C) (hs1 : 1 ≤ s) (hns : (n : ℝ) ≤ C * s)
    (hsL : 4 * L / K < s) (hj : j ≤ n) (hj₁ : (j : ℝ) ≤ a * n) (hj₂ : a * n < j + 1)
    (hshape : (n : ℝ) * G0 - 2 * L ≤ gd) :
    {ω : Environment | ∃ q : Path (0 : Lattice) (j, n - j),
      gd - K / (2 * C) * (n : ℝ) ≤ pathWeight ω q ∧
      ∀ i, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
        |((q.vertex i).1 : ℝ) - (((0 : Lattice).1 : ℝ) + t * (j : ℝ))| +
          |((q.vertex i).2 : ℝ) - (((0 : Lattice).2 : ℝ) + t * ((n - j : ℕ) : ℝ))| ≤
          min (1 / 4 : ℝ) (4 / C) * (n : ℝ)} ⊆ crossing a G0 K s n := by
  rintro ω ⟨q, hw, htube⟩
  refine ⟨⟨⟨j, Nat.lt_succ_of_le hj⟩, q⟩, fun v => ?_, ?_⟩
  · obtain ⟨t, ht0, ht1, hdev⟩ := htube v
    have hcoord := floor_point_transverse a n j hj
    have hd : |(1 - a) * (j : ℝ) - a * ((n - j : ℕ) : ℝ)| ≤ 1 := by
      rw [hcoord, abs_le]
      constructor <;> linarith
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hB : min (1 / 4 : ℝ) (4 / C) * (n : ℝ) ≤ 4 * s :=
      calc min (1 / 4 : ℝ) (4 / C) * (n : ℝ) ≤ 4 / C * (n : ℝ) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hnn
        _ ≤ 4 / C * (C * s) := mul_le_mul_of_nonneg_left hns (by positivity)
        _ = 4 * s := by
            rw [div_mul_eq_mul_div, div_eq_iff hC.ne']
            ring
    simp only [Prod.fst_zero, Prod.snd_zero, Int.cast_zero] at hdev
    exact transverse_tube_bound a t _ _ (j : ℝ) ((n - j : ℕ) : ℝ) _ s ha₀ ha₁ ht0 ht1
      hd hdev hB hs1
  · exact weight_strict K C s L G0 gd _ (n : ℝ) hK hC hns hsL hshape hw

/-- Step 1 of the proof of Proposition 4.3 of the differentiability preprint: the shape at
`(j, n - j)` is within `2 L` of `n g(ξ)`. -/
private theorem shape_lower (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ z w : Quadrant,
      |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤
        (min a (1 - a) - min a (1 - a) / 2) * ((z.1 : ℝ) + (z.2 : ℝ)) ∧
      |(1 - a) * (w.1 : ℝ) - a * (w.2 : ℝ)| ≤
        (min a (1 - a) - min a (1 - a) / 2) * ((w.1 : ℝ) + (w.2 : ℝ)) →
      |g z - g w| ≤ L * (|(z.1 : ℝ) - (w.1 : ℝ)| + |(z.2 : ℝ) - (w.2 : ℝ)|))
    (n j : ℕ) (hj : j ≤ n) (hj₁ : (j : ℝ) ≤ a * n) (hj₂ : a * n < j + 1)
    (hcone : 1 ≤ min a (1 - a) / 2 * (n : ℝ)) :
    (n : ℝ) * g (toQuadrant (a, 1 - a)) - 2 * L ≤ g ((j : ℝ≥0), ((n - j : ℕ) : ℝ≥0)) := by
  have hcoord := floor_point_transverse a n j hj
  have hjR : ((n - j : ℕ) : ℝ) = (n : ℝ) - j := Nat.cast_sub hj
  have hlev : (j : ℝ) + ((n - j : ℕ) : ℝ) = (n : ℝ) := by
    rw [hjR]
    ring
  have hgw : g ((n : ℝ≥0) • toQuadrant (a, 1 - a)) = n * g (toQuadrant (a, 1 - a)) := by
    have := hhom (n : ℝ≥0) (toQuadrant (a, 1 - a))
    rw [NNReal.coe_natCast] at this
    exact this
  have hw1 : (((n : ℝ≥0) • toQuadrant (a, 1 - a)).1 : ℝ) = n * a := by
    simp [toQuadrant, Real.coe_toNNReal _ ha₀.le]
  have hw2 : (((n : ℝ≥0) • toQuadrant (a, 1 - a)).2 : ℝ) = n * (1 - a) := by
    simp [toQuadrant, Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ 1 - a)]
  have hmin : min a (1 - a) - min a (1 - a) / 2 = min a (1 - a) / 2 := by ring
  have hc₁ : |(1 - a) * (((j : ℝ≥0) : ℝ)) - a * ((((n - j : ℕ) : ℝ≥0) : ℝ))| ≤
      (min a (1 - a) - min a (1 - a) / 2) *
        ((((j : ℝ≥0) : ℝ)) + ((((n - j : ℕ) : ℝ≥0) : ℝ))) := by
    simp only [NNReal.coe_natCast]
    rw [hcoord, hlev, hmin, abs_le]
    constructor <;> linarith
  have hc₂ : |(1 - a) * (((n : ℝ≥0) • toQuadrant (a, 1 - a)).1 : ℝ) -
      a * (((n : ℝ≥0) • toQuadrant (a, 1 - a)).2 : ℝ)| ≤
      (min a (1 - a) - min a (1 - a) / 2) *
        ((((n : ℝ≥0) • toQuadrant (a, 1 - a)).1 : ℝ) +
          (((n : ℝ≥0) • toQuadrant (a, 1 - a)).2 : ℝ)) := by
    rw [hw1, hw2]
    have h0 : (1 - a) * (n * a) - a * (n * (1 - a)) = 0 := by ring
    have h1 : (n : ℝ) * a + n * (1 - a) = n := by ring
    rw [h0, h1, abs_zero, hmin]
    linarith
  have hcomp := hLip ((j : ℝ≥0), ((n - j : ℕ) : ℝ≥0)) ((n : ℝ≥0) • toQuadrant (a, 1 - a))
    ⟨hc₁, hc₂⟩
  have hcomp' : |g ((j : ℝ≥0), ((n - j : ℕ) : ℝ≥0)) - n * g (toQuadrant (a, 1 - a))| ≤
      L * (|(j : ℝ) - n * a| + |((n : ℝ) - j) - n * (1 - a)|) := by
    rw [← hgw]
    simpa only [NNReal.coe_natCast, hw1, hw2, hjR] using hcomp
  have hD : |(j : ℝ) - n * a| + |((n : ℝ) - j) - n * (1 - a)| ≤ 2 := by
    have e : ((n : ℝ) - j) - n * (1 - a) = -((j : ℝ) - n * a) := by ring
    rw [e, abs_neg, mul_comm (n : ℝ) a]
    have : |(j : ℝ) - a * n| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hLD := mul_le_mul_of_nonneg_left hD hL
  have h2 := (abs_le.1 hcomp').1
  linarith

/-- Large lengths (steps 1 to 5 of the proof of Proposition 4.3 of the differentiability preprint):
the travel lemma at scale `n`. -/
private theorem large_length_crossing (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : Quadrant → ℝ) (hcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (htravel : TravelFor μ g) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (K C : ℝ)
    (hK : 0 < K) (hC : 0 < C) (c : ℝ) (hc : c < 1) :
    ∃ N : ℕ, ∃ s0 : ℝ, ∀ s : ℝ, s0 ≤ s → ∀ n : ℕ, N ≤ n → (n : ℝ) ≤ C * s →
      c < (environmentLaw μ).real
        (crossing a (g (toQuadrant (a, 1 - a))) K s n) := by
  have hθ : 0 < min a (1 - a) := lt_min ha₀ (by linarith)
  have hθa : min a (1 - a) ≤ a := min_le_left _ _
  have hθb : min a (1 - a) ≤ 1 - a := min_le_right _ _
  obtain ⟨L, hL, hLip⟩ := quadrant_homogeneous_shape_lipschitz_on_adapted_cone g hcont
    hconc hhom a (min a (1 - a) / 2) ha₀ ha₁ (by positivity) (by linarith)
  have hη : 0 < K / (2 * C) := by positivity
  have hδ : 0 < min (1 / 4 : ℝ) (4 / C) := lt_min (by norm_num) (by positivity)
  obtain ⟨s1, hs1, p, -, hpt, htrav⟩ := htravel a ha₀ ha₁ 1 le_rfl (min a (1 - a) / 2)
    (by positivity) (by linarith) (K / (2 * C)) (min (1 / 4 : ℝ) (4 / C)) hη hδ
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hpt.eventually (lt_mem_nhds hc))
  refine ⟨⌈max (max s1 M) (2 / min a (1 - a))⌉₊, max 1 (4 * L / K + 1), ?_⟩
  intro s hs n hn hns
  have hs1' : 1 ≤ s := (le_max_left _ _).trans hs
  have hsL : 4 * L / K < s := by linarith [(le_max_right _ _).trans hs]
  have hnR : max (max s1 M) (2 / min a (1 - a)) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hs1n : s1 ≤ (n : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hnR)
  have hMn : M ≤ (n : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hnR)
  have hn2 : 2 / min a (1 - a) ≤ (n : ℝ) := (le_max_right _ _).trans hnR
  have hone : 1 ≤ min a (1 - a) / 2 * (n : ℝ) := by
    have := (div_le_iff₀ hθ).1 hn2
    linarith
  obtain ⟨hj, hj₁, hj₂⟩ := floor_point_facts a ha₀ ha₁ n
  generalize ⌊a * (n : ℝ)⌋₊ = j at hj hj₁ hj₂
  have hcoord := floor_point_transverse a n j hj
  have hlev : (j : ℝ) + ((n - j : ℕ) : ℝ) = (n : ℝ) := by
    rw [Nat.cast_sub hj]
    ring
  have hinter : |(1 - a) * (((j, n - j) : ℕ × ℕ).1 : ℝ) - a * (((j, n - j) : ℕ × ℕ).2 : ℝ)| ≤
      (min a (1 - a) - min a (1 - a) / 2) *
        ((((j, n - j) : ℕ × ℕ).1 : ℝ) + (((j, n - j) : ℕ × ℕ).2 : ℝ)) := by
    show |(1 - a) * (j : ℝ) - a * ((n - j : ℕ) : ℝ)| ≤
      (min a (1 - a) - min a (1 - a) / 2) * ((j : ℝ) + ((n - j : ℕ) : ℝ))
    rw [hcoord, hlev, abs_le]
    constructor <;> linarith
  have hlevN : ((((j, n - j) : ℕ × ℕ).1 + ((j, n - j) : ℕ × ℕ).2 : ℕ) : ℝ) = (n : ℝ) := by
    show ((j + (n - j) : ℕ) : ℝ) = (n : ℝ)
    rw [Nat.add_sub_cancel' hj]
  obtain ⟨-, hprob⟩ := htrav (n : ℝ) 0 (j, n - j) hs1n hlevN.ge
    (by rw [hlevN]; linarith) hinter
  have hshape := shape_lower g hhom a ha₀ ha₁ L (by linarith) hLip n j hj hj₁ hj₂ hone
  exact lt_of_lt_of_le (hM n hMn) (hprob.trans (measureReal_mono
    (travel_subset a K C s L (g (toQuadrant (a, 1 - a))) _ n j ha₀ ha₁ hK hC hs1' hns
      hsL hj hj₁ hj₂ hshape)))

/-- A crossing that starts at the origin is a crossing with a free start on level zero (as in the
proof of Proposition 3.4 of the differentiability preprint: `x_0` is any site on level `0` with
`|r(x_0)| ≤ 8 s`). -/
private theorem crossing_subset_free (a G0 K s : ℝ) (n : ℕ) :
    crossing a G0 K s n ⊆ {ω : Environment | ∃ u : Lattice, u.1 + u.2 = 0 ∧
      ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s) ∧
          G0 * (n : ℝ) - K * s < pathWeight ω q} := by
  rintro ω ⟨⟨i, q⟩, h₁, h₂⟩
  refine ⟨0, by simp, (i.val, n - i.val), ?_, q, h₁, h₂⟩
  have := i.isLt
  show i.val + (n - i.val) = n
  omega

/-- Proposition 4.3 of the differentiability preprint, (4.4): for the unique shape `g`, every
`K, C > 0` and `c < 1`, for all large `s`, every integer `n` with `1 ≤ n ≤ C s` has crossing
probability (as a real number, `measureReal`) above `c`. The crossing event is the preprint's
`E(s, n)`: some admissible path from a site `u` of level zero to a site of level `n`, with
transverse coordinate at most `8 s` in absolute value at every vertex and weight above
`g(a, 1 - a) n - K s`. -/
theorem short_crossing_abundance
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
      (∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
        (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ)) ∧
      (∀ a : ℝ, 0 < a → a < 1 → ∀ K C : ℝ, 0 < K → 0 < C → ∀ c : ℝ, c < 1 →
        ∃ s0 : ℝ, ∀ s : ℝ, s0 ≤ s → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ C * s →
          c < (environmentLaw μ).real {ω : Environment |
            ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
              (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s) ∧
                g (toQuadrant (a, 1 - a)) * (n : ℝ) - K * s < pathWeight ω q}) := by
  obtain ⟨g, hg, _⟩ := exists_unique_shape_with_travel μ hneg hpos
  obtain ⟨_g0, _hg0, hunique⟩ :=
    exists_unique_shape_of_negative_moment_and_positive_tail μ hneg hpos
  refine ⟨g, ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, ?_⟩, ?_⟩
  · intro a ha₀ ha₁ K C hK hC c hc
    obtain ⟨N, s0, hbig⟩ := large_length_crossing μ g hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.2
      a ha₀ ha₁ K C hK hC c hc
    have hsmall : ∀ᶠ s in atTop, ∀ n ∈ Finset.range N,
        c < (environmentLaw μ).real (crossing a (g (toQuadrant (a, 1 - a))) K s n) :=
      (Filter.eventually_all_finset (Finset.range N)).2 fun n _ =>
        small_length_crossing μ a _ K ha₀ ha₁ hK n c hc
    obtain ⟨s2, hs2⟩ := eventually_atTop.1 hsmall
    refine ⟨max s0 s2, fun s hs n _ hnC => ?_⟩
    refine lt_of_lt_of_le ?_ (measureReal_mono (crossing_subset_free a (g (toQuadrant (a, 1 - a))) K s n))
    by_cases hN : N ≤ n
    · exact hbig s ((le_max_left _ _).trans hs) n hN hnC
    · exact hs2 s ((le_max_right _ _).trans hs) n (Finset.mem_range.2 (not_le.1 hN))
  · intro f hf
    exact (hunique f ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩).trans
      (hunique g ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1⟩).symm

end LPPDifferentiability
