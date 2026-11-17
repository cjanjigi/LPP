/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProbabilityBasics.Analysis.JointHilbertCoboundaries

/-! Approximation by a joint fixed vector and two directional coboundaries. -/

@[expose] public section

namespace ProbabilityBasics

/-- Every vector in a real Hilbert space can be approximated by a joint fixed
vector and two coboundaries for arbitrary contractions. This is the Hilbert
approximation step of Krengel, Ergodic Theorems, §1.1 Lemma 1.3 and §6.2 Theorem 2.8.
The coefficients are unrestricted; the sum of the coboundary ranges need not be closed. -/
theorem exists_joint_fixed_add_coboundaries_approx
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (U0 U1 : E →L[ℝ] E) (h0 : ‖U0‖ ≤ 1) (h1 : ‖U1‖ ≤ 1)
    (f : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ g a b : E, U0 g = g ∧ U1 g = g ∧
      ‖f - (g + (a - U0 a) + (b - U1 b))‖ < ε := by
  let A0 : E →ₗ[ℝ] E := (1 : E →ₗ[ℝ] E) - U0.toLinearMap
  let A1 : E →ₗ[ℝ] E := (1 : E →ₗ[ℝ] E) - U1.toLinearMap
  let F : Submodule ℝ E := LinearMap.ker A0 ⊓ LinearMap.ker A1
  let N : Submodule ℝ E := LinearMap.range A0 ⊔ LinearMap.range A1
  -- The joint fixed space is closed, so Hilbert projection applies internally.
  have hClosed : IsClosed (F : Set E) := by
    change IsClosed
      ((((1 : E →L[ℝ] E) - U0).ker : Set E) ∩
        (((1 : E →L[ℝ] E) - U1).ker : Set E))
    exact ((1 : E →L[ℝ] E) - U0).isClosed_ker.inter
      ((1 : E →L[ℝ] E) - U1).isClosed_ker
  let : IsClosed (F : Set E) := hClosed
  obtain ⟨g, hg, hResidual⟩ :=
    Submodule.HasOrthogonalProjection.exists_orthogonal (K := F) f
  have hFixed0 : U0 g = g := by
    have hZero : g - U0 g = 0 := hg.1
    exact (sub_eq_zero.mp hZero).symm
  have hFixed1 : U1 g = g := by
    have hZero : g - U1 g = 0 := hg.2
    exact (sub_eq_zero.mp hZero).symm
  -- The closure identity puts this residual in the actual sum closure.
  have hClosure : N.topologicalClosure = Fᗮ :=
    joint_coboundary_closure_eq_fixed_orthogonal U0 U1 h0 h1
  have hResidualClosure : f - g ∈ closure (N : Set E) := by
    have hMem : f - g ∈ N.topologicalClosure := by
      rw [hClosure]
      exact hResidual
    change f - g ∈ (N.topologicalClosure : Set E) at hMem
    rwa [Submodule.topologicalClosure_coe] at hMem
  obtain ⟨c, hc, hClose⟩ := (Metric.mem_closure_iff.mp hResidualClosure) ε hε
  -- Sup membership supplies two actual range witnesses, without closed ranges.
  obtain ⟨u, hu, v, hv, hSum⟩ := Submodule.mem_sup.mp hc
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  have hCoboundaries : (a - U0 a) + (b - U1 b) = c := by
    change A0 a + A1 b = c
    rw [ha, hb]
    exact hSum
  refine ⟨g, a, b, hFixed0, hFixed1, ?_⟩
  have hError : f - (g + (a - U0 a) + (b - U1 b)) = (f - g) - c := by
    rw [add_assoc, hCoboundaries, sub_add_eq_sub_sub]
  rw [hError]
  simpa only [dist_eq_norm] using hClose

end ProbabilityBasics
