/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.DirectionalAssembly
import ProbabilityBasics.Analysis.ConcaveProfileContact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The profile of the shape at the edges of a flat segment

The deterministic part of the differentiability of the shape function at the edges of a flat
segment. The profile is `ḡ(t) = g(t, 1 - t)` on `[0, 1]`, written with the quadrant
extension.

* `exists_nonpos_supporting_line_of_flat_edge`: if `ḡ ≤ 1` and `ḡ(β) = 1`, then at every
  `p` with `β < p < 1` the concave profile has a supporting line with slope at most `0`.
* `differentiableAt_flat_edges_of_chord_bound`: if `ḡ = 1` on `[1 - β, β]` with
  `1/2 ≤ β < 1`, `g` is symmetric, and the chord slopes of `ḡ` to the right of `β` come
  arbitrarily close to `0` from below, then the quadrant extension is differentiable at
  `(β, 1 - β)` and at `(1 - β, β)`.

## References

- Georgiou, Rassoul-Agha and Seppäläinen (manuscript in preparation), the flat-edge theorem.
- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint, Theorem 2.2(b) and (c).
-/

public section

open Set Filter
open scoped Topology NNReal

namespace LPPDifferentiability

/-- The profile at `a`, evaluated at the offset `y - a`, is `ḡ(y)`. -/
private theorem profile_at_offset (g : Quadrant → ℝ) (a y : ℝ) :
    quadrantExtension g (a + (y - a), 1 - a - (y - a)) = quadrantExtension g (y, 1 - y) := by
  have e1 : a + (y - a) = y := by ring
  have e2 : 1 - a - (y - a) = 1 - y := by ring
  rw [e1, e2]

/-- The profile at `1 - a` is the mirror image of the profile at `a`, by the symmetry
`g (x₂, x₁) = g x`. -/
private theorem profile_reflect (g : Quadrant → ℝ) (hswap : ∀ x : Quadrant, g (x.2, x.1) = g x)
    (a : ℝ) :
    (fun h : ℝ => quadrantExtension g (1 - a + h, 1 - (1 - a) - h)) =
      (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h)) ∘ Neg.neg := by
  funext h
  simp only [Function.comp_apply, quadrantExtension, toQuadrant]
  have e1 : 1 - (1 - a) - h = a + -h := by ring
  have e2 : 1 - a + h = 1 - a - -h := by ring
  rw [e1, e2]
  exact hswap ((a + -h).toNNReal, (1 - a - -h).toNNReal)

/-- A right derivative of the profile at `a` gives the opposite left derivative of the
profile at `1 - a`. -/
private theorem hasDerivWithinAt_profile_reflect_Iio (g : Quadrant → ℝ)
    (hswap : ∀ x : Quadrant, g (x.2, x.1) = g x) (a v : ℝ)
    (hv : HasDerivWithinAt (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h)) v (Ioi 0) 0) :
    HasDerivWithinAt (fun h : ℝ => quadrantExtension g (1 - a + h, 1 - (1 - a) - h)) (-v)
      (Iio 0) 0 := by
  rw [profile_reflect g hswap a]
  have hv' : HasDerivWithinAt (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h)) v (Ioi 0)
      (-0) := by
    rwa [neg_zero]
  have hc := hv'.comp 0 (hasDerivWithinAt_neg 0 (Iio 0))
    (fun x (hx : x < 0) => (neg_pos.mpr hx : 0 < -x))
  rwa [mul_neg_one] at hc

/-- A left derivative of the profile at `a` gives the opposite right derivative of the
profile at `1 - a`. -/
private theorem hasDerivWithinAt_profile_reflect_Ioi (g : Quadrant → ℝ)
    (hswap : ∀ x : Quadrant, g (x.2, x.1) = g x) (a v : ℝ)
    (hv : HasDerivWithinAt (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h)) v (Iio 0) 0) :
    HasDerivWithinAt (fun h : ℝ => quadrantExtension g (1 - a + h, 1 - (1 - a) - h)) (-v)
      (Ioi 0) 0 := by
  rw [profile_reflect g hswap a]
  have hv' : HasDerivWithinAt (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h)) v (Iio 0)
      (-0) := by
    rwa [neg_zero]
  have hc := hv'.comp 0 (hasDerivWithinAt_neg 0 (Ioi 0))
    (fun x (hx : 0 < x) => (neg_lt_zero.mpr hx : -x < 0))
  rwa [mul_neg_one] at hc

/-- **Supporting line with nonpositive slope.** Let the profile `ḡ(y) = g(y, 1 - y)` of a
concave `g` satisfy `ḡ ≤ 1` on `[0, 1]` and `ḡ(β) = 1`. At every `p` with `β < p < 1` there
is a line through `(p, ḡ(p))` with slope `σ ≤ 0` lying above `ḡ` on `[0, 1]`.

This is the supporting-line step of the proof of Jensen's inequality, at the deterministic
point `p`. -/
theorem exists_nonpos_supporting_line_of_flat_edge (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (β p : ℝ) (hβ₀ : 0 ≤ β) (hβp : β < p) (hp₁ : p < 1)
    (hβ : quadrantExtension g (β, 1 - β) = 1)
    (hle : ∀ y ∈ Icc (0 : ℝ) 1, quadrantExtension g (y, 1 - y) ≤ 1) :
    ∃ σ : ℝ, σ ≤ 0 ∧ ∀ y ∈ Icc (0 : ℝ) 1,
      quadrantExtension g (y, 1 - y) ≤ quadrantExtension g (p, 1 - p) + σ * (y - p) := by
  have hp₀ : 0 < p := by linarith
  -- The profile around `p` is concave on `[-p, 1 - p]`.
  have hconc := concaveOn_quadrantExtension_profile g hgconc p
  -- Its right-derivative line supports it.
  have hsupp := (ConcaveOn.supporting_lines_and_one_sided_contact hconc
    (by linarith : -p < 0) (by linarith : (0 : ℝ) < 1 - p)).2.1
  obtain ⟨σ, hσdef⟩ : ∃ σ, derivWithin (fun h : ℝ => quadrantExtension g (p + h, 1 - p - h))
      (Ioi 0) 0 = σ := ⟨_, rfl⟩
  have hline : ∀ y ∈ Icc (0 : ℝ) 1,
      quadrantExtension g (y, 1 - y) ≤ quadrantExtension g (p, 1 - p) + σ * (y - p) := by
    intro y hy
    have hb : quadrantExtension g (p + (y - p), 1 - p - (y - p)) ≤
        quadrantExtension g (p + 0, 1 - p - 0) +
          derivWithin (fun h : ℝ => quadrantExtension g (p + h, 1 - p - h)) (Ioi 0) 0 *
            (y - p) :=
      hsupp (y - p) ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rw [profile_at_offset, add_zero, sub_zero, hσdef] at hb
    exact hb
  refine ⟨σ, ?_, hline⟩
  -- The slope is nonpositive: the line is at least `1` at `β < p`, while `ḡ(p) ≤ 1`.
  have hatβ := hline β ⟨hβ₀, by linarith⟩
  rw [hβ] at hatβ
  have hatp := hle p ⟨hp₀.le, hp₁.le⟩
  by_contra hσ
  have hneg : σ * (β - p) < 0 := mul_neg_of_pos_of_neg (not_le.mp hσ) (by linarith)
  linarith

/-- **Differentiability at the two edges from a chord bound.** Let `g` be homogeneous,
concave and symmetric, `1/2 ≤ β < 1`, and `ḡ = 1` on `[1 - β, β]`. Suppose that for every
`ε > 0` some `h ∈ (0, 1 - β]` has `ḡ(β + h) ≥ 1 - ε h`. Then the right derivative of `ḡ`
at `β` is `0`, matching the left derivative (flatness, or the mirror symmetry when
`β = 1/2`), so the quadrant extension of `g` is differentiable at `(β, 1 - β)`, and by the
symmetry also at `(1 - β, β)`. -/
theorem differentiableAt_flat_edges_of_chord_bound (g : Quadrant → ℝ)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hswap : ∀ x : Quadrant, g (x.2, x.1) = g x)
    (β : ℝ) (hβhalf : 1 / 2 ≤ β) (hβone : β < 1)
    (hflat : ∀ t ∈ Icc (1 - β) β, g (toQuadrant (t, 1 - t)) = 1)
    (hchord : ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ h ≤ 1 - β ∧
      1 - ε * h ≤ quadrantExtension g (β + h, 1 - β - h)) :
    DifferentiableAt ℝ (quadrantExtension g) (β, 1 - β) ∧
      DifferentiableAt ℝ (quadrantExtension g) (1 - β, β) := by
  have hβ₀ : 0 < β := by linarith
  have hconc := concaveOn_quadrantExtension_profile g hgconc β
  have hP0 : quadrantExtension g (β + 0, 1 - β - 0) = 1 := by
    rw [add_zero, sub_zero]
    exact hflat β ⟨by linarith, le_rfl⟩
  -- The canonical one-sided derivatives `σ` (right) and `λ` (left) of the profile at `β`.
  obtain ⟨σ, hσdef⟩ : ∃ σ, derivWithin (fun h : ℝ => quadrantExtension g (β + h, 1 - β - h))
      (Ioi 0) 0 = σ := ⟨_, rfl⟩
  obtain ⟨l, hldef⟩ : ∃ l, derivWithin (fun h : ℝ => quadrantExtension g (β + h, 1 - β - h))
      (Iio 0) 0 = l := ⟨_, rfl⟩
  have hR := hasDerivWithinAt_profile_right g hgconc β hβ₀ hβone
  have hL := hasDerivWithinAt_profile_left g hgconc β hβ₀ hβone
  have horder := profile_rightDeriv_le_leftDeriv g hgconc β hβ₀ hβone
  rw [hσdef] at hR horder
  rw [hldef] at hL horder
  -- The right derivative is at least every chord slope, so the chord bound makes it
  -- nonnegative.
  have hσ_nonneg : 0 ≤ σ := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨h, hh₀, hh₁, hhc⟩ := hchord (ε / 2) (by linarith)
    have hslope : (quadrantExtension g (β + h, 1 - β - h) -
        quadrantExtension g (β + 0, 1 - β - 0)) / (h - 0) ≤ σ := by
      have hs := hconc.slope_le_of_hasDerivWithinAt_Ioi (x := 0) (y := h)
        ⟨by linarith, by linarith⟩ ⟨by linarith, hh₁⟩ hh₀ hR
      rwa [slope_def_field] at hs
    rw [hP0, sub_zero] at hslope
    have h1 : quadrantExtension g (β + h, 1 - β - h) - 1 ≤ σ * h := (div_le_iff₀ hh₀).mp hslope
    by_contra hcon
    have h2 : σ * h ≤ -ε * h := mul_le_mul_of_nonneg_right (by linarith) hh₀.le
    have h3 : 0 < ε * h := mul_pos hε hh₀
    linarith
  -- The left derivative is `0` (flat case) or `-σ` (case `β = 1/2`).
  have hkey : σ = 0 ∧ l = 0 := by
    rcases lt_or_eq_of_le hβhalf with hβgt | hβeq
    · have hconst : HasDerivWithinAt (fun h : ℝ => quadrantExtension g (β + h, 1 - β - h)) 0
          (Iio 0) 0 := by
        refine (hasDerivWithinAt_const (0 : ℝ) (Iio 0) (1 : ℝ)).congr_of_eventuallyEq ?_ hP0
        filter_upwards [Ioo_mem_nhdsLT (show 1 - 2 * β < 0 by linarith)] with h hh
        have e : 1 - β - h = 1 - (β + h) := by ring
        show quadrantExtension g (β + h, 1 - β - h) = 1
        rw [e]
        exact hflat (β + h) ⟨by linarith [hh.1], by linarith [hh.2]⟩
      have hl0 : l = 0 := (uniqueDiffWithinAt_Iio 0).eq_deriv _ hL hconst
      exact ⟨by linarith, hl0⟩
    · have hmirror := hasDerivWithinAt_profile_reflect_Iio g hswap β σ hR
      have e : 1 - β = β := by linarith
      rw [e] at hmirror
      have hl : l = -σ := (uniqueDiffWithinAt_Iio 0).eq_deriv _ hL hmirror
      constructor <;> linarith
  refine ⟨?_, ?_⟩
  -- The point `(β, 1 - β)`.
  · refine differentiableAt_quadrantExtension_of_profile_derivWithin_eq g hghom hgconc β hβ₀
      hβone ?_
    rw [hσdef, hldef, hkey.1, hkey.2]
  -- The point `(1 - β, β)`, by the mirror symmetry.
  · have hL' := hasDerivWithinAt_profile_reflect_Iio g hswap β σ hR
    have hR' := hasDerivWithinAt_profile_reflect_Ioi g hswap β l hL
    have hd := differentiableAt_quadrantExtension_of_profile_derivWithin_eq g hghom hgconc
      (1 - β) (by linarith) (by linarith)
      (by rw [hL'.derivWithin (uniqueDiffWithinAt_Iio 0),
        hR'.derivWithin (uniqueDiffWithinAt_Ioi 0), hkey.1, hkey.2])
    rwa [sub_sub_cancel] at hd

end LPPDifferentiability
