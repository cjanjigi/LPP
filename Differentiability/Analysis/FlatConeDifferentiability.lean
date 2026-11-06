/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.Quadrant
public import Mathlib.Analysis.Calculus.FDeriv.Prod
import LPP_Foundations.Analysis.HomogeneousRescaling
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Differentiability inside a flat cone

Positive homogeneity extends a constant value on a unit-sum interval to a
linear value on its cone. At points whose normalized coordinate is strictly
inside the interval, this equality holds on a neighborhood and gives the
Fréchet derivative of the actual quadrant extension.
-/

public section

open Filter Set ContinuousLinearMap
open scoped NNReal Topology

namespace LPPDifferentiability

private theorem quadrantExtension_eq_level_eventually
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (l r M : ℝ) (hl₀ : 0 ≤ l) (_hlr : l < r) (hr₁ : r ≤ 1)
    (hlevel : ∀ t ∈ Icc l r, g (toQuadrant (t, 1 - t)) = M)
    (x : ℝ × ℝ) (hx₁ : 0 < x.1) (hx₂ : 0 < x.2)
    (hinside : x.1 / (x.1 + x.2) ∈ Ioo l r) :
    quadrantExtension g =ᶠ[𝓝 x] fun y => M * (y.1 + y.2) := by
  have hsum : 0 < x.1 + x.2 := add_pos hx₁ hx₂
  have hratio : ContinuousAt (fun y : ℝ × ℝ => y.1 / (y.1 + y.2)) x :=
    continuousAt_fst.div (continuousAt_fst.add continuousAt_snd) hsum.ne'
  have hratio_mem :
      {y : ℝ × ℝ | y.1 / (y.1 + y.2) ∈ Ioo l r} ∈ 𝓝 x :=
    hratio.preimage_mem_nhds (Ioo_mem_nhds hinside.1 hinside.2)
  have h₁ : {y : ℝ × ℝ | 0 < y.1} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hx₁
  have h₂ : {y : ℝ × ℝ | 0 < y.2} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hx₂
  filter_upwards [hratio_mem, h₁, h₂] with y hratio_y hy₁ hy₂
  let c : ℝ≥0 := Real.toNNReal (y.1 + y.2)
  let t : ℝ := y.1 / (y.1 + y.2)
  have hysum : 0 < y.1 + y.2 := add_pos hy₁ hy₂
  have hc : (c : ℝ) = y.1 + y.2 := by
    change (Real.toNNReal (y.1 + y.2) : ℝ) = y.1 + y.2
    exact Real.coe_toNNReal _ hysum.le
  have hcoords : 1 - t = y.2 / (y.1 + y.2) := by
    dsimp [t]
    field_simp [hysum.ne']
    ring
  have hscale : c • (t, 1 - t) = y := by
    apply Prod.ext
    · change (c : ℝ) * t = y.1
      rw [hc]
      dsimp [t]
      exact mul_div_cancel₀ y.1 hysum.ne'
    · change (c : ℝ) * (1 - t) = y.2
      rw [hc]
      rw [hcoords]
      exact mul_div_cancel₀ y.2 hysum.ne'
  have ht_nonneg : 0 ≤ t := le_trans hl₀ hratio_y.1.le
  have hsecond_nonneg : 0 ≤ 1 - t := by
    exact sub_nonneg.mpr (le_trans hratio_y.2.le hr₁)
  have hpoint : quadrantInclusion (toQuadrant (t, 1 - t)) = (t, 1 - t) :=
    quadrantInclusion_toQuadrant _ ht_nonneg hsecond_nonneg
  have hprofile : quadrantExtension g (t, 1 - t) = M := by
    rw [← hpoint, quadrantExtension_quadrantInclusion]
    exact hlevel t ⟨le_of_lt hratio_y.1, le_of_lt hratio_y.2⟩
  calc
    quadrantExtension g y =
        (c : ℝ) * quadrantExtension g (t, 1 - t) := by
      rw [← hscale, quadrantExtension_smul g hhom c (t, 1 - t)]
    _ = (c : ℝ) * M := by rw [hprofile]
    _ = M * (y.1 + y.2) := by
      rw [hc]
      ring

/-- The actual quadrant extension has the expected Fréchet derivative at
every positive point whose normalized coordinate lies strictly inside a flat
unit-sum interval. The neighborhood equality is derived in the proof from
homogeneity and the interval level condition. -/
theorem hasFDerivAt_quadrantExtension_of_flat_interval
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (l r M : ℝ) (hl₀ : 0 ≤ l) (_hlr : l < r) (hr₁ : r ≤ 1)
    (hlevel : ∀ t ∈ Icc l r, g (toQuadrant (t, 1 - t)) = M)
    (x : ℝ × ℝ) (hx₁ : 0 < x.1) (hx₂ : 0 < x.2)
    (hinside : x.1 / (x.1 + x.2) ∈ Ioo l r) :
    HasFDerivAt (quadrantExtension g)
      (M • (fst ℝ ℝ ℝ + snd ℝ ℝ ℝ)) x := by
  have hsum : HasFDerivAt (fun y : ℝ × ℝ => y.1 + y.2)
      (fst ℝ ℝ ℝ + snd ℝ ℝ ℝ) x :=
    hasFDerivAt_fst.add hasFDerivAt_snd
  have hlinear : HasFDerivAt (fun y : ℝ × ℝ => M * (y.1 + y.2))
      (M • (fst ℝ ℝ ℝ + snd ℝ ℝ ℝ)) x :=
    hsum.const_mul M
  exact hlinear.congr_of_eventuallyEq
    (quadrantExtension_eq_level_eventually g hhom l r M hl₀ _hlr hr₁ hlevel
      x hx₁ hx₂ hinside)

/-- Differentiability of the actual quadrant extension follows at every
positive point whose normalized coordinate lies strictly inside the flat
unit-sum interval. -/
theorem differentiableAt_quadrantExtension_of_flat_interval
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (l r M : ℝ) (hl₀ : 0 ≤ l) (_hlr : l < r) (hr₁ : r ≤ 1)
    (hlevel : ∀ t ∈ Icc l r, g (toQuadrant (t, 1 - t)) = M)
    (x : ℝ × ℝ) (hx₁ : 0 < x.1) (hx₂ : 0 < x.2)
    (hinside : x.1 / (x.1 + x.2) ∈ Ioo l r) :
    DifferentiableAt ℝ (quadrantExtension g) x :=
  (hasFDerivAt_quadrantExtension_of_flat_interval g hhom l r M hl₀ _hlr hr₁
    hlevel x hx₁ hx₂ hinside).differentiableAt

/-- The same actual derivative at a positive unit-sum point in the interval. -/
theorem hasFDerivAt_quadrantExtension_on_flat_interval
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (l r M : ℝ) (hl₀ : 0 ≤ l) (_hlr : l < r) (hr₁ : r ≤ 1)
    (hlevel : ∀ t ∈ Icc l r, g (toQuadrant (t, 1 - t)) = M)
    (a : ℝ) (ha : a ∈ Ioo l r) :
    HasFDerivAt (quadrantExtension g)
      (M • (fst ℝ ℝ ℝ + snd ℝ ℝ ℝ)) (a, 1 - a) := by
  have ha₀ : 0 < a := lt_of_le_of_lt hl₀ ha.1
  have ha₁ : a < 1 := lt_of_lt_of_le ha.2 hr₁
  have hsum : a + (1 - a) = 1 := by ring
  have hinside : (a, 1 - a).1 / ((a, 1 - a).1 + (a, 1 - a).2) ∈ Ioo l r := by
    change a / (a + (1 - a)) ∈ Ioo l r
    rw [hsum, div_one]
    exact ha
  exact hasFDerivAt_quadrantExtension_of_flat_interval g hhom l r M hl₀ _hlr hr₁
    hlevel (a, 1 - a) ha₀ (sub_pos.mpr ha₁) hinside

/-- Differentiability at the positive unit-sum point in the flat interval. -/
theorem differentiableAt_quadrantExtension_on_flat_interval
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (l r M : ℝ) (hl₀ : 0 ≤ l) (_hlr : l < r) (hr₁ : r ≤ 1)
    (hlevel : ∀ t ∈ Icc l r, g (toQuadrant (t, 1 - t)) = M)
    (a : ℝ) (ha : a ∈ Ioo l r) :
    DifferentiableAt ℝ (quadrantExtension g) (a, 1 - a) :=
  (hasFDerivAt_quadrantExtension_on_flat_interval g hhom l r M hl₀ _hlr hr₁
    hlevel a ha).differentiableAt

end LPPDifferentiability
