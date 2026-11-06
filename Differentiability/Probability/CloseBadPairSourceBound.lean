/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.FiniteBadPairs
public import Differentiability.Model.FiniteCloseLatticePairs
public import Differentiability.Model.HeavyAttachmentRegionCardinality
import Mathlib.Tactic

/-! The finite-region E1 failure bound in the heavy attachment argument. -/
public section
open MeasureTheory Set
namespace LPPDifferentiability

/-- The literal close-bad-pair event has the source's twelve-per-site bound. -/
theorem environmentLaw_real_close_bad_pair_le_twelve
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (Q : Finset Lattice) (T : ℝ) :
    (environmentLaw μ).real (⋃ uv ∈
      (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
        |(uv.1.1 : ℝ) - (uv.2.1 : ℝ)| + |(uv.1.2 : ℝ) - (uv.2.2 : ℝ)| ≤ 2),
      {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}) ≤
      12 * (Q.card : ℝ) * (μ.real (Iio (-T))) ^ 2 := by
  classical
  have hcard :
      (((Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
        |(uv.1.1 : ℝ) - (uv.2.1 : ℝ)| +
        |(uv.1.2 : ℝ) - (uv.2.2 : ℝ)| ≤ 2)).card : ℝ) ≤
      12 * (Q.card : ℝ) := by
    have h := lattice_close_pairs_card_le_twelve_mul Q
    simp only [abs_sub_comm] at h ⊢
    exact_mod_cast h
  exact (environmentLaw_real_close_bad_pair_union_le μ Q T).trans
    (mul_le_mul_of_nonneg_right hcard (sq_nonneg _))

/-- Conditional geometric-cap corollary; the cardinal premise is supplied by
an actual region construction in the joint theorem below. -/
theorem environmentLaw_real_close_bad_pair_le_of_card_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (Q : Finset Lattice) (T D s : ℝ)
    (hQ : (Q.card : ℝ) ≤ 4 * D * s ^ 2) :
    (environmentLaw μ).real (⋃ uv ∈
      (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
        |(uv.1.1 : ℝ) - (uv.2.1 : ℝ)| + |(uv.1.2 : ℝ) - (uv.2.2 : ℝ)| ≤ 2),
      {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}) ≤
      48 * D * s ^ 2 * (μ.real (Iio (-T))) ^ 2 := by
  calc
    _ ≤ 12 * (Q.card : ℝ) * (μ.real (Iio (-T))) ^ 2 :=
      environmentLaw_real_close_bad_pair_le_twelve μ Q T
    _ ≤ (12 * (4 * D * s ^ 2)) * (μ.real (Iio (-T))) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ (by norm_num))
        (sq_nonneg _)
    _ = _ := by ring

/-- One actual source region supplies membership, cardinality, measurability
and the close-bad-pair estimate with the same finite witness. -/
theorem exists_finset_heavy_attachment_region_close_bad_pair_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T a D s kappa rho1 rho2 : ℝ)
    (I : ℤ) (K : ℕ)
    (hD : 1 ≤ D) (hs : 4 ≤ s) (hkappa : 0 < kappa)
    (hkappaCap : kappa ≤ (1 / 16 : ℝ))
    (hrange : rho1 ≤ rho2) (hwidth : rho2-rho1 ≤ D*s)
    (hcut : 2*(K:ℝ)+5 ≤ (Nat.ceil (kappa*s) : ℝ)) :
    ∃ Q : Finset Lattice,
      (∀ z, z ∈ Q ↔
        I ≤ z.1+z.2 ∧ z.1+z.2 ≤ I+(Nat.ceil (kappa*s) : ℤ) ∧
        rho1-(Nat.ceil (kappa*s) : ℝ)-(K:ℝ)-2 ≤
          (1-a)*(z.1:ℝ)-a*(z.2:ℝ) ∧
        (1-a)*(z.1:ℝ)-a*(z.2:ℝ) ≤
          rho2+(Nat.ceil (kappa*s) : ℝ)+(K:ℝ)+2) ∧
      (Q.card : ℝ) ≤ 4 * D * s ^ 2 ∧
      MeasurableSet (⋃ uv ∈
      (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
        |(uv.1.1 : ℝ) - (uv.2.1 : ℝ)| + |(uv.1.2 : ℝ) - (uv.2.2 : ℝ)| ≤ 2),
      {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}) ∧
      (environmentLaw μ).real (⋃ uv ∈
      (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
        |(uv.1.1 : ℝ) - (uv.2.1 : ℝ)| + |(uv.1.2 : ℝ) - (uv.2.2 : ℝ)| ≤ 2),
      {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}) ≤
        48 * D * s ^ 2 * (μ.real (Iio (-T))) ^ 2 := by
  classical
  obtain ⟨Q, hmem, hcard⟩ := exists_finset_heavy_attachment_region
    a D s kappa rho1 rho2 I K hD hs hkappa hkappaCap hrange hwidth hcut
  exact ⟨Q, hmem, hcard, measurableSet_close_bad_pair_union Q T,
    environmentLaw_real_close_bad_pair_le_of_card_le μ Q T D s hcard⟩

end LPPDifferentiability
end
