/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.PositiveQuadrantDensity
public import Martin2004.Analysis.RationalRateMeanCorrection
public import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Unique continuous extension on the interior

The same rational function, defined on the whole nonnegative rational quadrant,
has a unique continuous extension to the interior. No chosen extension
or values on the axes are defined here.
-/

public section

open scoped NNRat NNReal Topology
open Filter Set Topology

namespace LPPDifferentiability

set_option quotPrecheck false in
local notation "ratInterior" =>
  (fun q : NNRatPairInterior =>
    (Subtype.mk (nnratPairToQuadrant q.val)
      (And.intro (NNRat.cast_pos.mpr q.property.1) (NNRat.cast_pos.mpr q.property.2)) : QuadrantInterior))

private theorem rational_interior_dense : DenseRange ratInterior := by
  apply Metric.denseRange_iff.mpr
  intro x ε hε
  obtain ⟨l, u, hl, hu, hld, hud⟩ := exists_positive_rational_brackets x ε hε
  refine ⟨l, ?_⟩
  change dist x.val (nnratPairToQuadrant l.val) < ε
  simpa only [dist_comm] using hld

/-- Around each interior point, one positive rational box gives a finite local
Lipschitz bound for the original signed function. -/
theorem nnrat_rate_local_bound_at_interior
    (F : (ℚ≥0 × ℚ≥0) → ℝ)
    (hhom : ∀ (c : ℚ≥0) (q : ℚ≥0 × ℚ≥0), F (c • q) = (c : ℝ) * F q)
    (hadd : ∀ q r : ℚ≥0 × ℚ≥0, F q + F r ≤ F (q + r))
    (m M : ℝ)
    (hlo : ∀ q : ℚ≥0 × ℚ≥0, m * ((q.1 : ℝ) + (q.2 : ℝ)) ≤ F q)
    (hup : ∀ q : ℚ≥0 × ℚ≥0, F q ≤ M * ((q.1 : ℝ) + (q.2 : ℝ)))
    (x : QuadrantInterior) :
    ∃ r > 0, ∃ K ≥ 0, ∀ p q : NNRatPairInterior,
      dist (ratInterior p) x < r → dist (ratInterior q) x < r →
      dist (F p.val) (F q.val) ≤ K * dist (ratInterior p) (ratInterior q) := by
  have hx₁ : 0 < (x.val.1 : ℝ) := x.property.1
  have hx₂ : 0 < (x.val.2 : ℝ) := x.property.2
  obtain ⟨a', ha'₀, ha'x⟩ := exists_rat_btwn (lt_min hx₁ hx₂)
  let a : ℚ≥0 := ⟨a', (Rat.cast_pos.mp ha'₀).le⟩
  have ha : 0 < a := Rat.cast_pos.mp ha'₀
  have hax₁ : (a : ℝ) < (x.val.1 : ℝ) := ha'x.trans_le (min_le_left _ _)
  have hax₂ : (a : ℝ) < (x.val.2 : ℝ) := ha'x.trans_le (min_le_right _ _)
  obtain ⟨b', hxb'⟩ := exists_rat_gt (max (x.val.1 : ℝ) (x.val.2 : ℝ))
  have hb'₀ : 0 < b' := Rat.cast_pos.mp (hx₁.trans ((le_max_left _ _).trans_lt hxb'))
  let b : ℚ≥0 := ⟨b', hb'₀.le⟩
  have hxb₁ : (x.val.1 : ℝ) < (b : ℝ) := (le_max_left _ _).trans_lt hxb'
  have hxb₂ : (x.val.2 : ℝ) < (b : ℝ) := (le_max_right _ _).trans_lt hxb'
  let r : ℝ := min (min ((x.val.1 : ℝ) - a) ((x.val.2 : ℝ) - a))
    (min ((b : ℝ) - x.val.1) ((b : ℝ) - x.val.2))
  have hr : 0 < r :=
    lt_min (lt_min (sub_pos.mpr hax₁) (sub_pos.mpr hax₂))
      (lt_min (sub_pos.mpr hxb₁) (sub_pos.mpr hxb₂))
  have hbox (p : NNRatPairInterior) (hp : dist (ratInterior p) x < r) :
      (a ≤ p.val.1 ∧ a ≤ p.val.2) ∧ (p.val.1 ≤ b ∧ p.val.2 ≤ b) := by
    have hd : max (|(p.val.1 : ℝ) - (x.val.1 : ℝ)|)
        (|(p.val.2 : ℝ) - (x.val.2 : ℝ)|) < r := hp
    have hd₁ := (le_max_left _ _).trans_lt hd
    have hd₂ := (le_max_right _ _).trans_lt hd
    have hr₁ : r ≤ (x.val.1 : ℝ) - a := (min_le_left _ _).trans (min_le_left _ _)
    have hr₂ : r ≤ (x.val.2 : ℝ) - a := (min_le_left _ _).trans (min_le_right _ _)
    have hr₃ : r ≤ (b : ℝ) - x.val.1 := (min_le_right _ _).trans (min_le_left _ _)
    have hr₄ : r ≤ (b : ℝ) - x.val.2 := (min_le_right _ _).trans (min_le_right _ _)
    rcases abs_lt.mp hd₁ with ⟨hd₁l, hd₁u⟩
    rcases abs_lt.mp hd₂ with ⟨hd₂l, hd₂u⟩
    refine ⟨⟨(NNRat.cast_le (K := ℝ)).mp ?_, (NNRat.cast_le (K := ℝ)).mp ?_⟩,
      ⟨(NNRat.cast_le (K := ℝ)).mp ?_, (NNRat.cast_le (K := ℝ)).mp ?_⟩⟩
    · linarith only [hd₁l, hr₁]
    · linarith only [hd₂l, hr₂]
    · linarith only [hd₁u, hr₃]
    · linarith only [hd₂u, hr₄]
  let K : ℝ := 2 * (b : ℝ) * (M - m) / (a : ℝ) + 2 * |m|
  refine ⟨r, hr, |K|, abs_nonneg K, ?_⟩
  intro p q hp hq
  obtain ⟨hpa, hpb⟩ := hbox p hp
  obtain ⟨hqa, hqb⟩ := hbox q hq
  have h := nnrat_rate_signed_mean_local_lipschitz F hhom hadd m M hlo hup
    a b ha p.val q.val hpa hpb hqa hqb
  change |F p.val - F q.val| ≤ |K| *
    max (|(p.val.1 : ℝ) - (q.val.1 : ℝ)|) (|(p.val.2 : ℝ) - (q.val.2 : ℝ)|)
  exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self K)
    (le_trans (abs_nonneg _) (le_max_left _ _)))

private theorem existsUnique_extension_of_local_bound
    {α X : Type*} [MetricSpace X] (i : α → X) (f : α → ℝ)
    (hdense : DenseRange i)
    (hlocal : ∀ x : X, ∃ r > 0, ∃ K ≥ 0, ∀ p q : α,
      dist (i p) x < r → dist (i q) x < r → dist (f p) (f q) ≤ K * dist (i p) (i q)) :
    ∃! G : X → ℝ, Continuous G ∧ ∀ p, G (i p) = f p := by
  let : TopologicalSpace α := TopologicalSpace.induced i inferInstance
  have di : IsDenseInducing i := ⟨IsInducing.induced i, hdense⟩
  have hlimits : ∀ x : X, ∃! y : ℝ, Tendsto f (comap i (𝓝 x)) (𝓝 y) := by
    intro x
    have : NeBot (comap i (𝓝 x)) := di.comap_nhds_neBot x
    have hc : Cauchy (map f (comap i (𝓝 x))) := by
      apply Metric.cauchy_iff.mpr
      refine ⟨inferInstance, ?_⟩
      intro ε hε
      obtain ⟨r, hr, K, hK, hbound⟩ := hlocal x
      let δ : ℝ := min r (ε / (2 * (K + 1)))
      have hδ : 0 < δ := lt_min hr (div_pos hε (by positivity))
      let s : Set α := {p | dist (i p) x < δ}
      have hs : s ∈ comap i (𝓝 x) := by
        exact preimage_mem_comap (Metric.ball_mem_nhds x hδ)
      refine ⟨f '' s, image_mem_map hs, ?_⟩
      rintro u ⟨p, hp, rfl⟩ v ⟨q, hq, rfl⟩
      have hp' : dist (i p) x < δ := hp
      have hq' : dist (i q) x < δ := hq
      have hdist : dist (i p) (i q) < 2 * δ := by
        have := dist_triangle (i p) x (i q)
        rw [dist_comm x (i q)] at this
        linarith only [this, hp', hq']
      have hsmall : 2 * (K + 1) * δ ≤ ε := by
        rw [mul_comm]
        exact (le_div_iff₀ (by positivity : 0 < 2 * (K + 1))).mp
          (show δ ≤ ε / (2 * (K + 1)) from min_le_right _ _)
      have hb := hbound p q (hp'.trans_le (min_le_left _ _))
        (hq'.trans_le (min_le_left _ _))
      have hmul := mul_le_mul_of_nonneg_left hdist.le hK
      nlinarith only [hb, hmul, hsmall, hδ]
    obtain ⟨y, hy⟩ := cauchy_map_iff_exists_tendsto.mp hc
    exact ⟨y, hy, fun z hz => tendsto_nhds_unique hz hy⟩
  have hexists : ∀ x : X, ∃ y : ℝ, Tendsto f (comap i (𝓝 x)) (𝓝 y) :=
    fun x => (hlimits x).exists
  -- Local limits are unique, so the extension below is well defined.
  refine ⟨di.extend f, ⟨di.continuous_extend hexists, di.extend_eq' hexists⟩, ?_⟩
  intro G hG
  exact (di.extend_unique hG.2 hG.1).symm

/-- The same rationally homogeneous superadditive function with signed linear
bounds has a unique continuous extension agreeing at every positive rational pair.
The theorem does not pick a particular extension and says nothing about the axes. -/
theorem existsUnique_continuous_nnrat_rate_interior_extension
    (F : (ℚ≥0 × ℚ≥0) → ℝ)
    (hhom : ∀ (c : ℚ≥0) (q : ℚ≥0 × ℚ≥0), F (c • q) = (c : ℝ) * F q)
    (hadd : ∀ q r : ℚ≥0 × ℚ≥0, F q + F r ≤ F (q + r))
    (m M : ℝ)
    (hlo : ∀ q : ℚ≥0 × ℚ≥0, m * ((q.1 : ℝ) + (q.2 : ℝ)) ≤ F q)
    (hup : ∀ q : ℚ≥0 × ℚ≥0, F q ≤ M * ((q.1 : ℝ) + (q.2 : ℝ))) :
    ∃! G : QuadrantInterior → ℝ,
      Continuous G ∧ ∀ q : NNRatPairInterior, G (ratInterior q) = F q.val := by
  exact existsUnique_extension_of_local_bound ratInterior (fun q => F q.val)
    rational_interior_dense (nnrat_rate_local_bound_at_interior F hhom hadd m M hlo hup)

/-- Every positive rational approximation converges to the value of any
continuous agreeing extension. In particular its values are Cauchy, independent
of which sequence or rational box was used. -/
theorem nnrat_rate_interior_approximation_tendsto
    (F : (ℚ≥0 × ℚ≥0) → ℝ) (G : QuadrantInterior → ℝ)
    (hG : Continuous G) (hagrees : ∀ q : NNRatPairInterior, G (ratInterior q) = F q.val)
    (x : QuadrantInterior) (q : ℕ → NNRatPairInterior)
    (hq : Tendsto (fun n => nnratPairToQuadrant (q n).val) atTop (𝓝 x.val)) :
    Tendsto (fun n => F (q n).val) atTop (𝓝 (G x)) ∧
      CauchySeq (fun n => F (q n).val) := by
  have hqi : Tendsto (fun n => ratInterior (q n)) atTop (𝓝 x) :=
    tendsto_subtype_rng.mpr hq
  have ht : Tendsto (fun n => G (ratInterior (q n))) atTop (𝓝 (G x)) :=
    (hG.tendsto x).comp hqi
  have heq : (fun n => G (ratInterior (q n))) = (fun n => F (q n).val) :=
    funext fun n => hagrees (q n)
  rw [heq] at ht
  exact ⟨ht, ht.cauchySeq⟩

end LPPDifferentiability
