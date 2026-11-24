/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.CrossingRemarks.Translation
import Differentiability.Model.Paths.DefectAlgebra
import all Differentiability.Probability.RarefastConnectors
import LPP_Foundations.Analysis.ShapeSupportingFunctionals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The shape threshold in Remark `rk:gversion` of the final differentiability draft. -/

public section

open LPPStatements MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability.FinalDraft

private theorem abs_transverse_displacement_le {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (a ρ B : ℝ)
    (hp : ∀ i, |stripTransverse a (p.vertex i) - ρ| ≤ B) :
    |stripTransverse a ((d.1 : ℤ), (d.2 : ℤ))| ≤ 2 * B := by
  have hstart := hp 0
  have hfinish := hp (Fin.last (d.1 + d.2))
  rw [p.start] at hstart
  rw [p.finish] at hfinish
  let z : Lattice := ((d.1 : ℤ), (d.2 : ℤ))
  have hdiff : stripTransverse a z =
      (stripTransverse a (u + z) - ρ) - (stripTransverse a u - ρ) := by
    have hdisplacement : stripTransverse a z = stripTransverse a (u + z) - stripTransverse a u := by
      change latticeTransverseCoordinate a z =
        latticeTransverseCoordinate a (u + z) - latticeTransverseCoordinate a u
      simpa only [add_sub_cancel_left] using latticeTransverseCoordinate_sub a (u + z) u
    rw [hdisplacement]
    ring
  rw [hdiff]
  exact (abs_sub _ _).trans (by linarith)

/-- A signed support crossing at a given excess also crosses above the shape at
that excess, since the support dominates the shape. -/
theorem strip_crossing_support_subset_shape
    (g : Quadrant → ℝ) (hghom : IsHomogeneous g) (hgconc : IsConcaveOnQuadrant g)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (I : ℤ) (ρ B excess : ℝ) (n : ℕ) (right : Bool) :
    stripCrossingEvent a I ρ B n (fun d => crossingSupport g a right d + excess) ⊆
      stripCrossingEvent a I ρ B n (fun d => g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) + excess) := by
  have hsupp := (quadrant_supporting_functionals_and_contact g
    (fun x y r t h => hgconc x y r t h) (fun c z => hghom c z) a ha₀ ha₁).1
  intro ω
  rintro ⟨u, hu, d, hd, p, hstrip, hweight⟩
  have hle : g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) ≤ crossingSupport g a right d := by
    rcases hsupp ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) with ⟨hminus, hplus⟩
    cases right
    · simpa [crossingSupport, stripTransverse, quadrantInclusion] using hminus
    · simpa [crossingSupport, stripTransverse, quadrantInclusion] using hplus
  refine ⟨u, hu, d, hd, p, hstrip, ?_⟩
  change crossingSupport g a right d + excess < pathWeight ω p at hweight
  change g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) + excess < pathWeight ω p
  linarith

private theorem exists_strip_support_gap
    (g : Quadrant → ℝ) (hghom : IsHomogeneous g) (hgconc : IsConcaveOnQuadrant g)
    (a κ : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hκ : 0 < κ) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ d : ℕ × ℕ, 0 < d.1 + d.2 →
      |stripTransverse a ((d.1 : ℤ), (d.2 : ℤ))| ≤ h₀ * ((d.1 : ℝ) + (d.2 : ℝ)) →
      ∃ right : Bool, crossingSupport g a right d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) ≤
        κ * |stripTransverse a ((d.1 : ℤ), (d.2 : ℤ))| := by
  have hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z :=
    fun c z => hghom c z
  have hconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r • x + t • y) :=
    fun x y r t h => hgconc x y r t h
  obtain ⟨hm, hmpos, hminus⟩ := exists_contact_radius g hconc hhom a (-1) κ ha₀ ha₁ (.inr rfl) hκ
  obtain ⟨hp, hppos, hplus⟩ := exists_contact_radius g hconc hhom a 1 κ ha₀ ha₁ (.inl rfl) hκ
  let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
  refine ⟨min hm hp, lt_min hmpos hppos, fun d hn hsmall => ?_⟩
  let r := stripTransverse a ((d.1 : ℤ), (d.2 : ℤ))
  have hr : (1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ) = r := by
    simp [r, stripTransverse]
  change |r| ≤ min hm hp * ((d.1 : ℝ) + (d.2 : ℝ)) at hsmall
  rcases lt_trichotomy r 0 with hneg | hzero | hpos
  · refine ⟨false, ?_⟩
    have hside : 0 < (-1 : ℝ) * r := by linarith
    have hnear : (-1 : ℝ) * r ≤ hm * ((d.1 : ℝ) + (d.2 : ℝ)) := by
      rw [neg_one_mul, ← abs_of_neg hneg]
      exact hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
    have hc : ∀ h : ℝ, 0 < (-1 : ℝ) * h → (-1 : ℝ) * h ≤ hm →
        H 0 + derivWithin H (Iio 0) 0 * h - H h ≤ κ * |h| := by
      norm_num [H] at hminus ⊢
      exact hminus
    have hgap := shape_gap_le g hhom a (-1) (H 0) (derivWithin H (Iio 0) 0) κ hm hc
      d.1 d.2 hn (by rwa [hr]) (by rwa [hr])
    rw [hr] at hgap
    simpa [crossingSupport, H, r] using hgap
  · refine ⟨false, ?_⟩
    have hdz : (((d.1 : ℝ≥0), (d.2 : ℝ≥0)) : Quadrant) ≠ 0 := by
      intro h0
      have h₁ : (d.1 : ℝ≥0) = 0 := congrArg Prod.fst h0
      have h₂ : (d.2 : ℝ≥0) = 0 := congrArg Prod.snd h0
      simp only [Nat.cast_eq_zero] at h₁ h₂
      omega
    obtain ⟨-, -, hval⟩ := quadrant_homogeneous_profile_normalization g hhom a _ hdz
    have hshape : g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) = ((d.1 : ℝ) + (d.2 : ℝ)) * H 0 := by
      simpa only [NNReal.coe_natCast, hr, hzero, zero_div, H] using hval
    change H 0 * ((d.1 : ℝ) + (d.2 : ℝ)) + derivWithin H (Iio 0) 0 * r -
      g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) ≤ κ * |r|
    rw [hshape, hzero]
    simp [mul_comm]
  · refine ⟨true, ?_⟩
    have hside : 0 < (1 : ℝ) * r := by simpa only [one_mul] using hpos
    have hnear : (1 : ℝ) * r ≤ hp * ((d.1 : ℝ) + (d.2 : ℝ)) := by
      rw [one_mul, ← abs_of_pos hpos]
      exact hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
    have hc : ∀ h : ℝ, 0 < (1 : ℝ) * h → (1 : ℝ) * h ≤ hp →
        H 0 + derivWithin H (Ioi 0) 0 * h - H h ≤ κ * |h| := by
      norm_num [H] at hplus ⊢
      exact hplus
    have hgap := shape_gap_le g hhom a 1 (H 0) (derivWithin H (Ioi 0) 0) κ hp hc
      d.1 d.2 hn (by rwa [hr]) (by rwa [hr])
    rw [hr] at hgap
    simpa [crossingSupport, H, r] using hgap

/-- Remark `rk:gversion`. Beyond one positive length-to-width ratio, a path
beating the shape by `ε*s` beats one of its own-side supports by `(ε/2)*s`.
All three strip events use the same center and width. -/
theorem strip_crossing_shape_subset_support_union
    (g : Quadrant → ℝ) (hghom : IsHomogeneous g) (hgconc : IsConcaveOnQuadrant g)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (s : ℝ) (n : ℕ), 0 < s → D * s ≤ (n : ℝ) →
      ∀ (I : ℤ) (ρ : ℝ),
        stripCrossingEvent a I ρ (R * s) n
            (fun d => g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) + ε * s) ⊆
          stripCrossingEvent a I ρ (R * s) n (fun d => crossingSupport g a false d + (ε / 2) * s) ∪
            stripCrossingEvent a I ρ (R * s) n (fun d => crossingSupport g a true d + (ε / 2) * s) := by
  let κ := ε / (4 * R)
  have hκ : 0 < κ := div_pos hε (by positivity)
  obtain ⟨h₀, hh₀, hgap⟩ := exists_strip_support_gap g hghom hgconc a κ ha₀ ha₁ hκ
  let D := 2 * R / h₀
  have hD : 0 < D := div_pos (by positivity) hh₀
  have hDh : h₀ * D = 2 * R := mul_div_cancel₀ _ hh₀.ne'
  have hκR : κ * (2 * R) = ε / 2 := by
    dsimp [κ]
    rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity : 4 * R ≠ 0) (by norm_num)]
    ring
  refine ⟨D, hD, fun s n hs hn I ρ => ?_⟩
  intro ω
  rintro ⟨u, hu, d, hd, p, hstrip, hweight⟩
  have hnpos : 0 < (n : ℝ) := (mul_pos hD hs).trans_le hn
  have hdpos : 0 < d.1 + d.2 := by rw [hd]; exact_mod_cast hnpos
  have hdreal : (d.1 : ℝ) + (d.2 : ℝ) = n := by exact_mod_cast hd
  let r := stripTransverse a ((d.1 : ℤ), (d.2 : ℤ))
  have hr : |r| ≤ 2 * (R * s) := abs_transverse_displacement_le p a ρ _ hstrip
  have hsmall : |r| ≤ h₀ * ((d.1 : ℝ) + (d.2 : ℝ)) := by
    rw [hdreal]
    calc
      |r| ≤ 2 * (R * s) := hr
      _ = (2 * R) * s := (mul_assoc _ _ _).symm
      _ = (h₀ * D) * s := by rw [hDh]
      _ = h₀ * (D * s) := mul_assoc _ _ _
      _ ≤ h₀ * (n : ℝ) := mul_le_mul_of_nonneg_left hn hh₀.le
  obtain ⟨right, hside⟩ := hgap d hdpos hsmall
  have hbound : κ * |r| ≤ (ε / 2) * s := by
    calc
      κ * |r| ≤ κ * (2 * (R * s)) := mul_le_mul_of_nonneg_left hr hκ.le
      _ = κ * ((2 * R) * s) := by rw [mul_assoc (2 : ℝ)]
      _ = (κ * (2 * R)) * s := (mul_assoc _ _ _).symm
      _ = (ε / 2) * s := by rw [hκR]
  have hfast : crossingSupport g a right d + (ε / 2) * s < pathWeight ω p := by
    change g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) + ε * s < pathWeight ω p at hweight
    linarith [hside.trans hbound]
  cases right
  · exact Or.inl ⟨u, hu, d, hd, p, hstrip, hfast⟩
  · exact Or.inr ⟨u, hu, d, hd, p, hstrip, hfast⟩

/-- Remark `rk:gversion` along any sequence of widths and lengths with
`s → ∞` and `n/s → ∞`. The crossing probability with the actual shape
threshold tends to zero for the original `R` and `ε`. -/
theorem rarefast_shape_crossing_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : HasNegativePartMomentAbove μ 1) (hpos : HasSqrtUpperTail μ)
    (g : Quadrant → ℝ) (hg : IsShapeFunction μ g) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) (s : ℕ → ℝ) (n : ℕ → ℕ)
    (hs : Tendsto s atTop atTop) (hns : Tendsto (fun k => (n k : ℝ) / s k) atTop atTop) :
    Tendsto (fun k => (environmentLaw μ).real (stripCrossingEvent a 0 0 (R * s k) (n k)
        (fun d => g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) + ε * s k))) atTop (𝓝 0) := by
  obtain ⟨D, -, hsub⟩ := strip_crossing_shape_subset_support_union g hg.2.1 hg.2.2.1
    a ha₀ ha₁ R ε hR hε
  refine tendsto_order.2 ⟨fun b hb => Eventually.of_forall fun _ => hb.trans_le measureReal_nonneg,
    fun b hb => ?_⟩
  obtain ⟨sm, hsmallm⟩ := rarefast_strip_uniform μ hneg hpos g hg a ha₀ ha₁
    R (ε / 2) hR (half_pos hε) false (b / 2) (half_pos hb)
  obtain ⟨sp, hsmallp⟩ := rarefast_strip_uniform μ hneg hpos g hg a ha₀ ha₁
    R (ε / 2) hR (half_pos hε) true (b / 2) (half_pos hb)
  filter_upwards [hs.eventually (eventually_ge_atTop sm), hs.eventually (eventually_ge_atTop sp),
    hs.eventually (eventually_ge_atTop (1 : ℝ)), hns.eventually (eventually_ge_atTop D)]
    with k hsm hsp hs1 hD
  have hspos : 0 < s k := zero_lt_one.trans_le hs1
  have hlong : D * s k ≤ (n k : ℝ) := (le_div_iff₀ hspos).mp hD
  have hprob := (measureReal_mono (μ := environmentLaw μ)
    (hsub (s k) (n k) hspos hlong 0 0) (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  exact hprob.trans_lt (by linarith [hsmallm (s k) (n k) hsm, hsmallp (s k) (n k) hsp])

end LPPDifferentiability.FinalDraft
