/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.Covering
public import LPP_Foundations.Model.Animals.CenterCount
public import ProbabilityBasics.Probability.BernoulliExponential

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Bernoulli tails for actual lattice animals

The planar cover, center count, finite union bound, and exponential Markov
calculation in Martin (2002), Proposition 2.2.
The event is expressed by existence of an animal, without introducing a maximum.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- The actual existence event is a countable union of measurable finite-sum
events, including when there are no animals satisfying the deterministic data. -/
theorem measurableSet_exists_animal_sum_ge {Ω : Type*} [MeasurableSpace Ω]
    (X : Lattice → Ω → ℝ) (hX : ∀ v, Measurable (X v)) (n : ℕ) (t : ℝ) :
    MeasurableSet {ω | ∃ s : Finset Lattice, IsConnectedAnimal s ∧
      (0 : Lattice) ∈ s ∧ s.card = n ∧ t ≤ ∑ v ∈ s, X v ω} := by
  classical
  simp only [← exists_prop, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro s
  apply MeasurableSet.iUnion
  intro _
  apply MeasurableSet.iUnion
  intro _
  apply MeasurableSet.iUnion
  intro _
  exact measurableSet_le measurable_const (Finset.measurable_sum s (fun v _ => hX v))

/-- The fixed-set Bernoulli bound with a genuine upper bound on its number of
distinct sites. The global independence assumption is restricted inside the proof. -/
theorem measureReal_finset_sum_ge_le_exp_card_bound {Ω V : Type*}
    [MeasurableSpace Ω] [DecidableEq V] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : V → Ω → ℝ) (hInd : iIndepFun X μ) (hX : ∀ v, Measurable (X v))
    (h01 : ∀ v, ∀ᵐ ω ∂μ, X v ω = 0 ∨ X v ω = 1)
    (p : ℝ) (hp : ∀ v, μ.real {ω | X v ω = 1} = p) (hp0 : 0 ≤ p)
    (U : Finset V) (K : ℕ) (hUK : U.card ≤ K) (t : ℝ) (ht : 0 < t) :
    μ.real {ω | t ≤ ∑ v ∈ U, X v ω} ≤
      Real.exp (-t + p * (Real.exp 1 - 1) * (K : ℝ)) := by
  classical
  have hbase : 1 ≤ 1 - p + p * Real.exp 1 := by
    have hexp : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith only [hp0, hexp]
  have hmoment : 1 - p + p * Real.exp 1 ≤ Real.exp (p * (Real.exp 1 - 1)) := by
    convert Real.add_one_le_exp (p * (Real.exp 1 - 1)) using 1
    ring
  have htail := measureReal_finset_sum_ge_le_exp μ U X p t
    (iIndepFun.precomp Subtype.val_injective hInd)
    (fun v => hX v.1) (fun v => h01 v.1) (fun v => hp v.1) ht
  have hEvent : {ω | t ≤ ∑ v : {x // x ∈ U}, X v.1 ω} =
      {ω | t ≤ ∑ v ∈ U, X v ω} := by
    ext ω
    exact (congrArg (fun z : ℝ => t ≤ z)
      (Finset.sum_coe_sort U (fun v => X v ω))).to_iff
  rw [hEvent] at htail
  calc
    μ.real {ω | t ≤ ∑ v ∈ U, X v ω} ≤
        Real.exp (-t) * (1 - p + p * Real.exp 1) ^ U.card := htail
    _ ≤ Real.exp (-t) * (1 - p + p * Real.exp 1) ^ K :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hUK) (Real.exp_nonneg _)
    _ ≤ Real.exp (-t) * Real.exp (p * (Real.exp 1 - 1)) ^ K :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_trans (by norm_num) hbase) hmoment K)
        (Real.exp_nonneg _)
    _ = Real.exp (-t + p * (Real.exp 1 - 1) * (K : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

/-- Martin's planar Bernoulli cover tail for the actual measurable existence
event. Its premises describe only the field, its common Bernoulli law, and the
scale and threshold ranges; covers and all estimates are derived. -/
theorem measureReal_exists_animal_sum_ge_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Lattice → Ω → ℝ)
    (hInd : iIndepFun X μ) (hX : ∀ v, Measurable (X v))
    (h01 : ∀ v, ∀ᵐ ω ∂μ, X v ω = 0 ∨ X v ω = 1)
    (p : ℝ) (hp : ∀ v, μ.real {ω | X v ω = 1} = p)
    (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) (n l : ℕ) (_hn : 1 ≤ n)
    (hl : 1 ≤ l) (hln : l ≤ n) (t : ℝ) (ht : 0 < t) :
    μ.real {ω | ∃ s : Finset Lattice, IsConnectedAnimal s ∧
      (0 : Lattice) ∈ s ∧ s.card = n ∧ t ≤ ∑ v ∈ s, X v ω} ≤
      (9 ^ (2 * n / l) : ℝ) * Real.exp
        (-t + p * (Real.exp 1 - 1) * (((2 * n / l) + 1) * (4 * l + 1) ^ 2 : ℕ)) := by
  classical
  let r := 2 * n / l
  let K := (r + 1) * (4 * l + 1) ^ 2
  let U : centerSequenceFamily r → Finset Lattice := fun u =>
    (Finset.univ : Finset (Fin (r + 1))).biUnion
      (fun i => integerBox ((l : ℤ) * (u.1 i).1, (l : ℤ) * (u.1 i).2) (2 * l))
  let E : centerSequenceFamily r → Set Ω := fun u => {ω | t ≤ ∑ v ∈ U u, X v ω}
  let : Finite (centerSequenceFamily r) := finite_centerSequenceFamily r
  let : Fintype (centerSequenceFamily r) := Fintype.ofFinite _
  have hcard : Fintype.card (centerSequenceFamily r) ≤ 9 ^ r := by
    simpa only [Nat.card_eq_fintype_card] using natCard_centerSequenceFamily_le r
  have hUcard : ∀ u, (U u).card ≤ K := by
    intro u
    exact integerBox_scaledCover_union_card_le r l
      (fun i => ((l : ℤ) * (u.1 i).1, (l : ℤ) * (u.1 i).2))
  have hsub : {ω | ∃ s : Finset Lattice, IsConnectedAnimal s ∧
      (0 : Lattice) ∈ s ∧ s.card = n ∧ t ≤ ∑ v ∈ s, X v ω} ≤ᵐ[μ] ⋃ u, E u := by
    filter_upwards [ae_all_iff.2 h01] with ω hω
    rintro ⟨s, hs, hz, hsn, hsum⟩
    have hc := exists_animal_cover s hs hz l hl (by simpa only [hsn] using hln)
    rw [hsn] at hc
    obtain ⟨u, hu0, hustep, hcover, _⟩ := hc
    let c : centerSequenceFamily r :=
      ⟨u, (mem_centerSequenceFamily_iff r u).2 ⟨hu0, hustep⟩⟩
    apply Set.mem_iUnion.mpr
    refine ⟨c, le_trans hsum ?_⟩
    apply Finset.sum_le_sum_of_subset_of_nonneg hcover
    intro v _ _
    rcases hω v with hzero | hone
    · rw [hzero]
    · rw [hone]
      norm_num
  have htail : ∀ u, μ.real (E u) ≤
      Real.exp (-t + p * (Real.exp 1 - 1) * (K : ℝ)) := by
    intro u
    exact measureReal_finset_sum_ge_le_exp_card_bound μ X hInd hX h01 p hp hp0
      (U u) K (hUcard u) t ht
  calc
    μ.real {ω | ∃ s : Finset Lattice, IsConnectedAnimal s ∧
        (0 : Lattice) ∈ s ∧ s.card = n ∧ t ≤ ∑ v ∈ s, X v ω} ≤
        μ.real (⋃ u, E u) :=
      ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    _ ≤ ∑ u, μ.real (E u) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _u : centerSequenceFamily r,
        Real.exp (-t + p * (Real.exp 1 - 1) * (K : ℝ)) :=
      Finset.sum_le_sum (fun u _ => htail u)
    _ = (Fintype.card (centerSequenceFamily r) : ℝ) *
        Real.exp (-t + p * (Real.exp 1 - 1) * (K : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (9 ^ r : ℝ) * Real.exp (-t + p * (Real.exp 1 - 1) * (K : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact_mod_cast hcard

end LPPDifferentiability
