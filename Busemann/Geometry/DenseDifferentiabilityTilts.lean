/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProbabilityBasics.Analysis.DenseConcaveDifferentiability
public import LPP_Foundations.Analysis.ShapeProfileCalculus
public import Busemann.Frozen.Definitions.InteriorDirection
public import Busemann.Frozen.Definitions.SupportTilt
import Busemann.Geometry.ExtremeCoordinateTilts
import Busemann.Geometry.SupportIdentities
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

/-! Ambient differentiability points in every interior direction interval. -/

@[expose] public section
open Set LPPDifferentiability
open scoped NNReal

namespace LPP.Busemann

/-- Every interval of interior unit directions contains an ambient
quadrant-extension differentiability point. This supplies the dense directions
in GRS arXiv:1510.00860v1, proof of Theorem 2.1(i). -/
theorem exists_differentiable_direction_between
    (g : Quadrant → ℝ)
    (hconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    ∃ ξ : InteriorDirection, (ξ.1.1 : ℝ) ∈ Ioo a b ∧
      DifferentiableAt ℝ (quadrantExtension g) (quadrantInclusion ξ.1) := by
  have hc := concaveOn_quadrantExtension_profile g hconc 0
  have hc' : ConcaveOn ℝ (Icc (0 : ℝ) 1)
      (fun t : ℝ => quadrantExtension g (t, 1 - t)) := by
    simpa only [neg_zero, zero_add, sub_zero] using hc
  obtain ⟨t, ht, hdiff⟩ := exists_differentiableAt_of_concaveOn_Icc _ hc' a b ha hb hab
  have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
  have ht1 : t < 1 := lt_of_lt_of_le ht.2 hb
  let ξ : InteriorDirection := ⟨(Real.toNNReal t, Real.toNNReal (1 - t)), by
    constructor
    · exact Real.toNNReal_pos.mpr ht0
    constructor
    · exact Real.toNNReal_pos.mpr (sub_pos.mpr ht1)
    · rw [Real.coe_toNNReal _ ht0.le, Real.coe_toNNReal _ (sub_nonneg.mpr ht1.le)]
      ring⟩
  refine ⟨ξ, ?_, ?_⟩
  · simpa only [ξ, Real.coe_toNNReal _ ht0.le] using ht
  · have hshift : DifferentiableAt ℝ
        (fun h : ℝ => quadrantExtension g (t + h, 1 - t - h)) 0 := by
      have htrans : DifferentiableAt ℝ (fun h : ℝ => t + h) 0 :=
        differentiableAt_id.const_add t
      have hdiff' : DifferentiableAt ℝ
          (fun t : ℝ => quadrantExtension g (t, 1 - t)) (t + 0) := by
        simpa only [add_zero] using hdiff
      have h := hdiff'.comp (0 : ℝ) htrans
      change DifferentiableAt ℝ
        (fun x : ℝ => quadrantExtension g (t + x, 1 - (t + x))) 0 at h
      have heq : (fun x : ℝ => quadrantExtension g (t + x, 1 - (t + x))) =
          (fun x : ℝ => quadrantExtension g (t + x, 1 - t - x)) := by
        funext x
        apply congrArg (quadrantExtension g)
        apply Prod.ext
        · rfl
        · ring
      rw [heq] at h
      exact h
    have hambient := (differentiableAt_profile_iff_quadrantExtension g hhom t ht0 ht1).1 hshift
    have hpoint : quadrantInclusion ξ.1 = (t, 1 - t) := by
      change quadrantInclusion (toQuadrant (t, 1 - t)) = (t, 1 - t)
      exact quadrantInclusion_toQuadrant (t, 1 - t) ht0.le (sub_nonneg.mpr ht1.le)
    rw [hpoint]
    exact hambient

private noncomputable def directionProfileHomeomorph : InteriorDirection ≃ₜ Set.Ioo (0 : ℝ) 1 where
  toFun ξ := ⟨(ξ.1.1 : ℝ), by
    constructor
    · exact_mod_cast ξ.2.1
    · have hp : 0 < (ξ.1.2 : ℝ) := by exact_mod_cast ξ.2.2.1
      linarith only [ξ.2.2.2, hp]⟩
  invFun t := ⟨(Real.toNNReal t.1, Real.toNNReal (1 - t.1)), by
    constructor
    · exact Real.toNNReal_pos.mpr t.2.1
    constructor
    · exact Real.toNNReal_pos.mpr (sub_pos.mpr t.2.2)
    · rw [Real.coe_toNNReal _ t.2.1.le,
        Real.coe_toNNReal _ (sub_nonneg.mpr t.2.2.le)]
      ring⟩
  left_inv ξ := by
    apply Subtype.ext
    apply Prod.ext
    · exact Real.toNNReal_coe
    · have heq : 1 - (ξ.1.1 : ℝ) = (ξ.1.2 : ℝ) := by
        linarith only [ξ.2.2.2]
      change Real.toNNReal (1 - (ξ.1.1 : ℝ)) = ξ.1.2
      rw [heq, Real.toNNReal_coe]
  right_inv t := by
    apply Subtype.ext
    exact Real.coe_toNNReal _ t.2.1.le
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- There is one countable dense sequence of actual ambient differentiability
points. GRS arXiv:1510.00860v1, proof of Theorem 2.1(i), uses a dense subset of D. -/
theorem exists_dense_differentiability_directions
    (g : Quadrant → ℝ)
    (hconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z) :
    ∃ D : ℕ → InteriorDirection, DenseRange D ∧
      ∀ n, DifferentiableAt ℝ (quadrantExtension g) (quadrantInclusion (D n).1) := by
  classical
  let e := directionProfileHomeomorph
  let S : Set (Set.Ioo (0 : ℝ) 1) := {t |
    DifferentiableAt ℝ (quadrantExtension g) (quadrantInclusion (e.symm t).1)}
  let : Nonempty (Set.Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by constructor <;> norm_num⟩⟩
  have hDense : Dense S := by
    apply dense_of_exists_between
    intro a b hab
    obtain ⟨ξ, hξ, hdiff⟩ := exists_differentiable_direction_between
      g hconc hhom a.1 b.1 a.2.1.le b.2.2.le hab
    refine ⟨e ξ, ?_, ?_, ?_⟩
    · change DifferentiableAt ℝ (quadrantExtension g)
        (quadrantInclusion (e.symm (e ξ)).1)
      rw [e.symm_apply_apply]
      exact hdiff
    · exact hξ.1
    · exact hξ.2
  obtain ⟨T, hTS, hCount, hTDense⟩ := hDense.exists_countable_dense_subset
  obtain ⟨f, hf⟩ := hCount.exists_eq_range hTDense.nonempty
  have hFDense : DenseRange f := by
    change Dense (Set.range f)
    rw [← hf]
    exact hTDense
  refine ⟨e.symm ∘ f, e.symm.surjective.denseRange.comp hFDense e.symm.continuous, ?_⟩
  intro n
  have hfn : f n ∈ T := hf.symm ▸ Set.mem_range_self n
  exact hTS hfn

/-- At an ambient differentiability direction every support is exactly the
negative gradient. GRS arXiv:1510.00860v1, equations (2.6)-(2.7). -/
theorem supporting_tilt_eq_negative_fderiv
    (g : Quadrant → ℝ)
    (hconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (ξ : InteriorDirection)
    (hdiff : DifferentiableAt ℝ (quadrantExtension g) (quadrantInclusion ξ.1))
    (h : SupportTilt g) (hh : SupportsAt g ξ h.1) :
    h.1 = (-((fderiv ℝ (quadrantExtension g) (quadrantInclusion ξ.1)) ((1 : ℝ), 0)),
      -((fderiv ℝ (quadrantExtension g) (quadrantInclusion ξ.1)) (0, (1 : ℝ)))) := by
  let a : ℝ := (ξ.1.1 : ℝ)
  let U1 : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a)
  let U2 : ℝ → ℝ := fun t => quadrantExtension g (a, 1 - a + t)
  let F := fderiv ℝ (quadrantExtension g) (quadrantInclusion ξ.1)
  have hpoint : quadrantInclusion ξ.1 = (a, 1 - a) := by
    apply Prod.ext
    · rfl
    · change (ξ.1.2 : ℝ) = 1 - a
      dsimp only [a]
      linarith only [ξ.2.2.2]
  have hF : HasFDerivAt (quadrantExtension g) F (a, 1 - a) := by
    rw [← hpoint]
    exact hdiff.hasFDerivAt
  have hU1 : HasDerivAt U1 (F ((1 : ℝ), 0)) 0 := by
    have hcurve : HasDerivAt (fun t : ℝ => (a + t, 1 - a)) ((1 : ℝ), 0) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_add a).prodMk (hasDerivAt_const 0 (1 - a))
    have hBase : (a, 1 - a) = (a + 0, 1 - a) := by simp only [add_zero]
    exact hF.comp_hasDerivAt_of_eq 0 hcurve hBase
  have hU2 : HasDerivAt U2 (F (0, (1 : ℝ))) 0 := by
    have hcurve : HasDerivAt (fun t : ℝ => (a, 1 - a + t)) (0, (1 : ℝ)) 0 :=
      (hasDerivAt_const 0 a).prodMk ((hasDerivAt_id (0 : ℝ)).const_add (1 - a))
    have hBase : (a, 1 - a) = (a, 1 - a + 0) := by simp only [add_zero]
    exact hF.comp_hasDerivAt_of_eq 0 hcurve hBase
  have hd1L := hU1.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio 0)
  have hd1R := hU1.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0)
  have hd2L := hU2.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio 0)
  have hd2R := hU2.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0)
  have hExt := coordinate_extreme_tilts_support_and_order g hconc hhom ξ
  change SupportsAt g ξ (-derivWithin U1 (Iio 0) 0, -derivWithin U2 (Ioi 0) 0) ∧
    SupportsAt g ξ (-derivWithin U1 (Ioi 0) 0, -derivWithin U2 (Iio 0) 0) ∧
    ∀ k : ℝ × ℝ, SupportsAt g ξ k →
      -derivWithin U1 (Iio 0) 0 ≤ k.1 ∧ k.1 ≤ -derivWithin U1 (Ioi 0) 0 at hExt
  rw [hd1L, hd1R, hd2L, hd2R] at hExt
  exact supporting_tilts_eq_of_first_coord_eq g ξ h.1
    (-F ((1 : ℝ), 0), -F (0, (1 : ℝ))) hhom hh hExt.1
    (le_antisymm (hExt.2.2 h.1 hh).2 (hExt.2.2 h.1 hh).1)

end LPP.Busemann
