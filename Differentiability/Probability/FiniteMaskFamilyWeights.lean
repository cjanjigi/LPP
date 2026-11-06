/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.FiniteMaskPathWeights

/-!
# Finite mask-dependent path families

Partition the original finite product law according to its threshold mask.
On each part, apply the conditional estimate to the selected good paths
and then sum over the mask values.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LPPDifferentiability

/-- Partition the original product into actual threshold cubes, apply the
conditional estimate to each active member, and average their actual masses.
The selections and their goodness refer to exactly the same finite mask. -/
theorem finite_mask_family_weight_failure_le
    {I J : Type*} [Fintype I] [Fintype J]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p b t : ℝ)
    (hp : 1 < p) (hT : 0 < T)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T))) (hb : 0 < b) (ht : 0 < t)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞)
    (n N K : ℕ) (hK : 1 ≤ K) (hJ : Fintype.card J ≤ N)
    (active : (I → Bool) → J → Bool) (m : (I → Bool) → J → ℕ)
    (f : (a : I → Bool) → (j : J) → active a j = true → Fin (m a j) → I)
    (hlen : ∀ a j, active a j = true → m a j ≤ n)
    (hinj : ∀ a j h, Function.Injective (f a j h))
    (hgood : ∀ (a : I → Bool) (j : J) (h : active a j = true) (k : Fin (m a j)),
      a (f a j h k) = false) :
    let mask := fun x : I → ℝ => fun i => if x i < -T then true else false
    let E := {x : I → ℝ | ∃ j : J, if h : active (mask x) j = true then
      (∑ k, x (f (mask x) j h k)) <
        -2 * (∫ y, max (-y) 0 ∂μ) * m (mask x) j - (K - 1 : ℕ) * T - t else False}
    MeasurableSet E ∧ (Measure.pi (fun _ : I => μ)).real E ≤
      N * ((2 * n * (∫ y, (max (-y) 0) ^ p ∂μ) * b ^ (-p)) ^ K +
        Real.exp (-t ^ 2 / (2 * b * (2 * (∫ y, max (-y) 0 ∂μ) * n + t / 3)))) := by
  classical
  let P := Measure.pi (fun _ : I => μ)
  let mask := fun x : I → ℝ => fun i => if x i < -T then true else false
  let C := fun a : I → Bool => {x : I → ℝ | ∀ i, if a i then x i < -T else -T ≤ x i}
  let c : ℝ := ∫ y, max (-y) 0 ∂μ
  let R := (2 * n * (∫ y, (max (-y) 0) ^ p ∂μ) * b ^ (-p)) ^ K +
    Real.exp (-t ^ 2 / (2 * b * (2 * c * n + t / 3)))
  let D := fun (a : I → Bool) (j : J) => {x : I → ℝ |
    if h : active a j = true then
      (∑ k, x (f a j h k)) < -2 * c * m a j - (K - 1 : ℕ) * T - t else False}
  let F := fun a : I → Bool => ⋃ j : J, D a j
  let E := {x : I → ℝ | ∃ j : J, if h : active (mask x) j = true then
    (∑ k, x (f (mask x) j h k)) < -2 * c * m (mask x) j - (K - 1 : ℕ) * T - t else False}
  change MeasurableSet E ∧ P.real E ≤ N * R
  have hC (a : I → Bool) : MeasurableSet (C a) :=
    measurableSet_finite_threshold_mask_cube μ T hT a
  have hD (a : I → Bool) (j : J) : MeasurableSet (D a j) := by
    by_cases h : active a j = true
    · dsimp only [D]
      simp only [dite_eq_left h]
      exact measurableSet_lt
        (Finset.measurable_sum _ fun k _ => measurable_pi_apply (f a j h k)) measurable_const
    · simp only [D, dite_eq_right h, Set.ofPred_false, MeasurableSet.empty]
  have hF (a : I → Bool) : MeasurableSet (F a) := MeasurableSet.iUnion (hD a)
  have hfiber (a : I → Bool) : C a = mask ⁻¹' {a} :=
    finite_threshold_cube_eq_mask_fiber T a
  have hcover : (⋃ a : I → Bool, C a) = Set.univ := by
    ext x
    simp only [hfiber, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact ⟨mask x, rfl⟩
  have hdis : Pairwise (fun a a' => Disjoint (C a) (C a')) := by
    intro a a' haa
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' : mask x = a := by simpa only [hfiber a, Set.mem_preimage, Set.mem_singleton_iff] using hx
    have hy' : mask x = a' := by simpa only [hfiber a', Set.mem_preimage, Set.mem_singleton_iff] using hy
    exact haa (hx'.symm.trans hy')
  have hE : E = ⋃ a : I → Bool, C a ∩ F a := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hx
      refine ⟨mask x, ?_, ?_⟩
      · rw [hfiber]
        rfl
      · simpa only [E, F, D, Set.mem_iUnion, Set.mem_ofPred_eq] using hx
    · rintro ⟨a, hxa, hfa⟩
      have heq : mask x = a := by simpa only [hfiber a, Set.mem_preimage, Set.mem_singleton_iff] using hxa
      subst a
      simpa only [E, F, D, Set.mem_iUnion, Set.mem_ofPred_eq] using hfa
  have hEm : MeasurableSet E := by
    rw [hE]
    exact MeasurableSet.iUnion fun a => (hC a).inter (hF a)
  refine ⟨hEm, ?_⟩
  have hR : 0 ≤ R := by
    dsimp [R]
    apply add_nonneg
    · apply pow_nonneg
      have hmoment0 : 0 ≤ ∫ y, (max (-y) 0) ^ p ∂μ :=
        integral_nonneg fun y => Real.rpow_nonneg (le_max_right _ _) p
      positivity
    · exact Real.exp_nonneg _
  have hfixed (a : I → Bool) (hpos : 0 < P (C a)) :
      ((P (C a))⁻¹ • P.restrict (C a)).real (F a) ≤ N * R := by
    let ρ := (P (C a))⁻¹ • P.restrict (C a)
    have : IsProbabilityMeasure ρ := isProbabilityMeasure_finite_threshold_mask_normalized μ T hT a hpos
    have hDj (j : J) : ρ.real (D a j) ≤ R := by
      by_cases h : active a j = true
      · dsimp only [D]
        simp only [dite_eq_left h]
        exact finite_mask_selected_weight_failure_le μ T p b t hp hT hthreshold hb ht hmoment
          a hpos (m a j) n K (hlen a j h) hK (f a j h) (hinj a j h) (hgood a j h)
      · simpa only [D, dite_eq_right h, Set.ofPred_false, measureReal_empty] using hR
    calc
      ρ.real (F a) ≤ ∑ j : J, ρ.real (D a j) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : J, R := Finset.sum_le_sum fun j _ => hDj j
      _ = (Fintype.card J : ℝ) * R := by simp
      _ ≤ N * R := mul_le_mul_of_nonneg_right (by exact_mod_cast hJ) hR
  have hpiece (a : I → Bool) : P.real (C a ∩ F a) ≤ P.real (C a) * (N * R) := by
    by_cases hzero : P (C a) = 0
    · have hzero' : P (C a ∩ F a) = 0 := measure_mono_null Set.inter_subset_left hzero
      simp only [measureReal_def, hzero, hzero', ENNReal.toReal_zero, zero_mul, le_refl]
    · have hpos : 0 < P (C a) := bot_lt_iff_ne_bot.mpr hzero
      have hrestrict : (P.restrict (C a)).real (F a) = P.real (C a ∩ F a) := by
        rw [measureReal_restrict_apply (hF a), Set.inter_comm]
      rw [← hrestrict, finite_mask_restriction_real_eq_mass_mul μ T a hpos]
      exact mul_le_mul_of_nonneg_left (hfixed a hpos) measureReal_nonneg
  have hmass : (∑ a : I → Bool, P.real (C a)) = 1 := by
    rw [← measureReal_iUnion_fintype hdis hC, hcover]
    exact probReal_univ
  calc
    P.real E ≤ ∑ a : I → Bool, P.real (C a ∩ F a) := by
      rw [hE]
      exact measureReal_iUnion_fintype_le _
    _ ≤ ∑ a : I → Bool, P.real (C a) * (N * R) := Finset.sum_le_sum fun a _ => hpiece a
    _ = (∑ a : I → Bool, P.real (C a)) * (N * R) := (Finset.sum_mul _ _ _).symm
    _ = N * R := by rw [hmass, one_mul]

end LPPDifferentiability
