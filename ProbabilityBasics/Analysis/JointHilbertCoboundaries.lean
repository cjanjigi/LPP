/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Joint fixed spaces and the closure of directional coboundary ranges. -/

@[expose] public section

open scoped InnerProduct

namespace ProbabilityBasics

private theorem adjoint_fixed_of_fixed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (U : E →L[ℝ] E) (hU : ‖U‖ ≤ 1) (x : E) (hx : U x = x) :
    (U†) x = x := by
  have hAdjointNorm : ‖U†‖ ≤ 1 := by
    calc
      ‖U†‖ = ‖U‖ := ContinuousLinearMap.adjoint.norm_map U
      _ ≤ 1 := hU
  have hBound : ‖(U†) x‖ ≤ ‖x‖ := by
    simpa only [one_mul] using (U†).le_of_opNorm_le hAdjointNorm x
  apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ) hBound
  change inner ℝ ((U†) x) x = ‖x‖ ^ 2
  rw [ContinuousLinearMap.adjoint_inner_left, hx, real_inner_self_eq_norm_sq]

private theorem fixed_iff_adjoint_fixed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (U : E →L[ℝ] E) (hU : ‖U‖ ≤ 1) (x : E) :
    U x = x ↔ (U†) x = x := by
  constructor
  · exact adjoint_fixed_of_fixed U hU x
  · intro hx
    have hAdjointNorm : ‖U†‖ ≤ 1 := by
      calc
        ‖U†‖ = ‖U‖ := ContinuousLinearMap.adjoint.norm_map U
        _ ≤ 1 := hU
    have hFixed := adjoint_fixed_of_fixed (U†) hAdjointNorm x hx
    simpa only [ContinuousLinearMap.adjoint_adjoint] using hFixed

private theorem coboundary_range_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (U : E →L[ℝ] E) (hU : ‖U‖ ≤ 1) :
    (LinearMap.range ((1 : E →ₗ[ℝ] E) - U.toLinearMap))ᗮ =
      LinearMap.ker ((1 : E →ₗ[ℝ] E) - U.toLinearMap) := by
  change ((1 : E →L[ℝ] E) - U).rangeᗮ = ((1 : E →L[ℝ] E) - U).ker
  rw [ContinuousLinearMap.orthogonal_range]
  ext x
  change (((1 : E →L[ℝ] E) - U)†) x = 0 ↔ ((1 : E →L[ℝ] E) - U) x = 0
  rw [map_sub, ContinuousLinearMap.adjoint_one]
  change x - (U†) x = 0 ↔ x - U x = 0
  constructor
  · intro hx
    have hAdjointFixed : (U†) x = x := (sub_eq_zero.mp hx).symm
    have hFixed := (fixed_iff_adjoint_fixed U hU x).mpr hAdjointFixed
    exact sub_eq_zero.mpr hFixed.symm
  · intro hx
    have hFixed : U x = x := (sub_eq_zero.mp hx).symm
    have hAdjointFixed := (fixed_iff_adjoint_fixed U hU x).mp hFixed
    exact sub_eq_zero.mpr hAdjointFixed.symm

/-- For two real Hilbert contractions, the closure of the sum of their
coboundary ranges is the orthogonal complement of their joint fixed space.
This is Krengel, Ergodic Theorems, §1.1 Lemmas 1.2–1.3, used in §6.2 Theorem 2.8. -/
theorem joint_coboundary_closure_eq_fixed_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (U0 U1 : E →L[ℝ] E) (h0 : ‖U0‖ ≤ 1) (h1 : ‖U1‖ ≤ 1) :
    let A0 : E →ₗ[ℝ] E := (1 : E →ₗ[ℝ] E) - U0.toLinearMap
    let A1 : E →ₗ[ℝ] E := (1 : E →ₗ[ℝ] E) - U1.toLinearMap
    let F : Submodule ℝ E := LinearMap.ker A0 ⊓ LinearMap.ker A1
    let N : Submodule ℝ E := LinearMap.range A0 ⊔ LinearMap.range A1
    N.topologicalClosure = Fᗮ := by
  let A0 : E →ₗ[ℝ] E := (1 : E →ₗ[ℝ] E) - U0.toLinearMap
  let A1 : E →ₗ[ℝ] E := (1 : E →ₗ[ℝ] E) - U1.toLinearMap
  let F : Submodule ℝ E := LinearMap.ker A0 ⊓ LinearMap.ker A1
  let N : Submodule ℝ E := LinearMap.range A0 ⊔ LinearMap.range A1
  change N.topologicalClosure = Fᗮ
  -- Each one-operator range orthogonal is its actual fixed space.
  have hOrthogonal : Nᗮ = F := by
    dsimp only [N, F, A0, A1]
    rw [← Submodule.inf_orthogonal,
      coboundary_range_orthogonal U0 h0, coboundary_range_orthogonal U1 h1]
  -- The ambient Hilbert completeness supplies exactly the required closure.
  calc
    N.topologicalClosure = Nᗮᗮ := (Submodule.orthogonal_orthogonal_eq_closure N).symm
    _ = Fᗮ := congrArg (fun K : Submodule ℝ E => Kᗮ) hOrthogonal

end ProbabilityBasics
