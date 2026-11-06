/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.CopyJensen
public import ProbabilityBasics.Probability.DifferenceSignLaw
public import ProbabilityBasics.Probability.DifferenceMoment
public import ProbabilityBasics.Probability.FairSignFubini

/-!
# Independent centered finite-sum moments

The copy-Jensen, whole-vector sign-symmetry, fair-sign averaging and
product-difference estimates give the finite-sum bound.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- A finite independent centered real family with finite absolute rth moments
has an integrable sum and sum moment, with moment bound of constant `2^r`.
The endpoint `r = 1` and any finite subset of the family are included. -/
theorem integrable_and_integral_abs_rpow_sum_independent_centered_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Finset ι) (Z : ι → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) (hInd : iIndepFun Z P)
    {r : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hMoment : ∀ i ∈ s, Integrable (fun ω => |Z i ω| ^ r) P)
    (hmean : ∀ i ∈ s, (∫ ω, Z i ω ∂P) = 0) :
    Integrable (fun ω => ∑ i ∈ s, Z i ω) P ∧
      Integrable (fun ω => |∑ i ∈ s, Z i ω| ^ r) P ∧
      (∫ ω, |∑ i ∈ s, Z i ω| ^ r ∂P) ≤
        (2 : ℝ) ^ r * ∑ i ∈ s, (∫ ω, |Z i ω| ^ r ∂P) := by
  classical
  have hSum := integrable_sum_and_abs_rpow_of_moments P s Z
    (fun i _ => hZ i) hr1 hMoment
  refine ⟨hSum.1, hSum.2, ?_⟩
  let D : ι → Ω × Ω → ℝ := fun i p => Z i p.1 - Z i p.2
  let signs : Measure (ι → Bool) :=
    Measure.pi (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure)
  have hD (i : ι) : Measurable (D i) :=
    ((hZ i).comp measurable_fst).sub ((hZ i).comp measurable_snd)
  have hDM (i : ι) (hi : i ∈ s) :
      Integrable (fun p => |D i p| ^ r) (P.prod P) :=
    integrable_abs_sub_rpow_prod P P (hZ i) (hZ i) r hr1
      (hMoment i hi) (hMoment i hi)
  have hFair := integrable_and_integral_abs_rpow_sum_fair_sign_random_le
    (P.prod P) s D (fun i _ => hD i) hr1 hr2 hDM
  have hVectorMoment : Measurable (fun a : ι → ℝ => |∑ i ∈ s, a i| ^ r) :=
    (Real.continuous_rpow_const (zero_le_one.trans hr1)).measurable.comp
      (continuous_abs.measurable.comp
        (Finset.measurable_sum s (fun i _ => measurable_pi_apply i)))
  have hSign (ε : ι → Bool) :
      (∫ p, |∑ i ∈ s, D i p| ^ r ∂P.prod P) =
        ∫ p, |∑ i ∈ s, (if ε i then (1 : ℝ) else -1) * D i p| ^ r
          ∂P.prod P :=
    ((identDistrib_independent_copy_difference_sign P Z hZ hInd ε).comp
      hVectorMoment).integral_eq
  have hSym : (∫ p, |∑ i ∈ s, D i p| ^ r ∂P.prod P) ≤
      ∑ i ∈ s, (∫ p, |D i p| ^ r ∂P.prod P) := by
    calc
      (∫ p, |∑ i ∈ s, D i p| ^ r ∂P.prod P) =
          ∫ ε : ι → Bool, (∫ p, |∑ i ∈ s, D i p| ^ r ∂P.prod P)
            ∂signs := by
        simp only [integral_const, probReal_univ, one_smul]
      _ = ∫ ε : ι → Bool, ∫ p,
          |∑ i ∈ s, (if ε i then (1 : ℝ) else -1) * D i p| ^ r
            ∂P.prod P ∂signs := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hSign
      _ = ∫ z : (Ω × Ω) × (ι → Bool),
          |∑ i ∈ s, (if z.2 i then (1 : ℝ) else -1) * D i z.1| ^ r
            ∂(P.prod P).prod signs := (integral_prod_symm _ hFair.1).symm
      _ ≤ ∑ i ∈ s, (∫ p, |D i p| ^ r ∂P.prod P) := hFair.2
  calc
    (∫ ω, |∑ i ∈ s, Z i ω| ^ r ∂P) ≤
        ∫ p, |∑ i ∈ s, D i p| ^ r ∂P.prod P :=
      integral_abs_rpow_sum_le_integral_copy_difference P s Z
        (fun i _ => hZ i) hr1 hMoment hmean
    _ ≤ ∑ i ∈ s, (∫ p, |D i p| ^ r ∂P.prod P) := hSym
    _ ≤ ∑ i ∈ s, (2 : ℝ) ^ r * (∫ ω, |Z i ω| ^ r ∂P) := by
      apply Finset.sum_le_sum
      intro i hi
      have hpair := integral_abs_sub_rpow_prod_le P P (hZ i) (hZ i) r hr1
        (hMoment i hi) (hMoment i hi)
      calc
        (∫ p, |D i p| ^ r ∂P.prod P) ≤
            (2 : ℝ) ^ (r - 1) *
              ((∫ ω, |Z i ω| ^ r ∂P) + (∫ ω, |Z i ω| ^ r ∂P)) := hpair
        _ = (2 : ℝ) ^ r * (∫ ω, |Z i ω| ^ r ∂P) := by
          rw [Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
          ring
    _ = (2 : ℝ) ^ r * ∑ i ∈ s, (∫ ω, |Z i ω| ^ r ∂P) :=
      (Finset.mul_sum s (fun i => ∫ ω, |Z i ω| ^ r ∂P) ((2 : ℝ) ^ r)).symm

end LPPDifferentiability
