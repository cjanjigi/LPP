/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Basic

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds

/-! # Independent finite event counts

For a finite family of actual independent events, the probability that at
least `K` events occur is bounded by the number of `K`-element subsets times
the largest product probability for one such subset.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LPPDifferentiability

private theorem badCount_event_eq_powersetCard_union
    {Ω I : Type*} [Fintype I] [DecidableEq I]
    (E : I → Set Ω) (K : ℕ) :
    {ω : Ω | K ≤
      (@Finset.filter I (fun i => ω ∈ E i) (Classical.decPred _) Finset.univ).card} =
      ⋃ S ∈ Finset.univ.powersetCard K,
        {ω : Ω | ∀ i ∈ S, ω ∈ E i} := by
  classical
  ext ω
  constructor
  · intro hω
    let F : Finset I := Finset.univ.filter fun i => ω ∈ E i
    obtain ⟨S, hSF, hScard⟩ := Finset.exists_subset_card_eq (s := F) hω
    have hS : S ∈ Finset.univ.powersetCard K :=
      Finset.mem_powersetCard.mpr
        ⟨hSF.trans (Finset.filter_subset _ _), hScard⟩
    apply Set.mem_iUnion.mpr
    refine ⟨S, Set.mem_iUnion.mpr ⟨hS, ?_⟩⟩
    change ∀ i ∈ S, ω ∈ E i
    intro i hi
    have hiF : i ∈ F := hSF hi
    change i ∈ Finset.univ.filter (fun i => ω ∈ E i) at hiF
    exact (Finset.mem_filter.mp hiF).2
  · intro hω
    obtain ⟨S, hSrest⟩ := Set.mem_iUnion.mp hω
    obtain ⟨hS, hbad⟩ := Set.mem_iUnion.mp hSrest
    have hScard : S.card = K := (Finset.mem_powersetCard.mp hS).2
    change ∀ i ∈ S, ω ∈ E i at hbad
    let F : Finset I := Finset.univ.filter fun i => ω ∈ E i
    have hSF : S ⊆ F := by
      intro i hi
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hbad i hi
    calc
      K = S.card := hScard.symm
      _ ≤ F.card := Finset.card_le_card hSF

private theorem badInter_event_eq
    {Ω I : Type*} (E : I → Set Ω) (S : Finset I) :
    {ω : Ω | ∀ i ∈ S, ω ∈ E i} = ⋂ i ∈ S, E i := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]

private theorem measureReal_iIndepSet_biInter_le_pow
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    (P : Measure Ω) (E : I → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (hInd : iIndepSet E P)
    (q : ℝ) (hq : ∀ i, P.real (E i) ≤ q) (S : Finset I) :
    P.real (⋂ i ∈ S, E i) ≤ q ^ S.card := by
  have hprod := (iIndepSet_iff_meas_biInter hE).mp hInd S
  calc
    P.real (⋂ i ∈ S, E i) = ∏ i ∈ S, P.real (E i) := by
      change (P (⋂ i ∈ S, E i)).toReal = _
      rw [hprod, ENNReal.toReal_prod]
      rfl
    _ ≤ ∏ _i ∈ S, q :=
      Finset.prod_le_prod₀ (fun _ _ => measureReal_nonneg) (fun i _ => hq i)
    _ = q ^ S.card := by simp

/-- The event that at least `K` of a finite family of measurable events occur
is measurable. -/
theorem measurableSet_iIndepSet_badCount_ge
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    (E : I → Set Ω) (hE : ∀ i, MeasurableSet (E i)) (K : ℕ) :
    MeasurableSet {ω : Ω | K ≤
      (@Finset.filter I (fun i => ω ∈ E i) (Classical.decPred _) Finset.univ).card} := by
  classical
  rw [badCount_event_eq_powersetCard_union]
  exact Finset.measurableSet_biUnion _ fun S _ => by
    rw [badInter_event_eq]
    exact Finset.measurableSet_biInter S fun i _ => hE i

/-- The actual independent event count has the finite-subset probability bound.
The events may have unequal probabilities, each bounded above by `q`. -/
theorem measureReal_iIndepSet_badCount_ge_le_choose
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    (P : Measure Ω) (E : I → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (hInd : iIndepSet E P) (q : ℝ) (_hq0 : 0 ≤ q)
    (hq : ∀ i, P.real (E i) ≤ q) (K : ℕ) :
    P.real {ω : Ω | K ≤
      (@Finset.filter I (fun i => ω ∈ E i) (Classical.decPred _) Finset.univ).card} ≤
        (Nat.choose (Fintype.card I) K : ℝ) * q ^ K := by
  classical
  let subsets : Finset (Finset I) := Finset.univ.powersetCard K
  have hEvent := badCount_event_eq_powersetCard_union E K
  rw [hEvent]
  calc
    P.real (⋃ S ∈ subsets, {ω : Ω | ∀ i ∈ S, ω ∈ E i}) ≤
        ∑ S ∈ subsets, P.real {ω : Ω | ∀ i ∈ S, ω ∈ E i} :=
      measureReal_biUnion_finset_le subsets _
    _ ≤ ∑ _S ∈ subsets, q ^ K := by
      apply Finset.sum_le_sum
      intro S hS
      have hS' : S ∈ Finset.univ.powersetCard K := by simpa only [subsets] using hS
      have hScard : S.card = K := (Finset.mem_powersetCard.mp hS').2
      calc
        P.real {ω : Ω | ∀ i ∈ S, ω ∈ E i} ≤ q ^ S.card := by
          rw [badInter_event_eq]
          exact measureReal_iIndepSet_biInter_le_pow P E hE hInd q hq S
        _ = q ^ K := by rw [hScard]
    _ = (subsets.card : ℝ) * q ^ K := by simp
    _ = (Nat.choose (Fintype.card I) K : ℝ) * q ^ K := by
      simp only [subsets, Finset.card_powersetCard, Finset.card_univ]

/-- The finite-subset count bound implies the source's exact `(|I| q)^K`
bound, including `K = 0`, `K > |I|`, and the empty index type. -/
theorem measureReal_iIndepSet_badCount_ge_le_pow
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    (P : Measure Ω) (E : I → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (hInd : iIndepSet E P) (q : ℝ) (hq0 : 0 ≤ q)
    (hq : ∀ i, P.real (E i) ≤ q) (K : ℕ) :
    P.real {ω : Ω | K ≤
      (@Finset.filter I (fun i => ω ∈ E i) (Classical.decPred _) Finset.univ).card} ≤
        ((Fintype.card I : ℝ) * q) ^ K := by
  have hchoose :
      (Nat.choose (Fintype.card I) K : ℝ) ≤ (Fintype.card I : ℝ) ^ K := by
    exact_mod_cast Nat.choose_le_pow (Fintype.card I) K
  have hqpow : 0 ≤ q ^ K := pow_nonneg hq0 K
  calc
    P.real {ω : Ω | K ≤
        (@Finset.filter I (fun i => ω ∈ E i) (Classical.decPred _) Finset.univ).card} ≤
        (Nat.choose (Fintype.card I) K : ℝ) * q ^ K :=
      measureReal_iIndepSet_badCount_ge_le_choose P E hE hInd q hq0 hq K
    _ ≤ ((Fintype.card I : ℝ) ^ K) * q ^ K :=
      mul_le_mul_of_nonneg_right hchoose hqpow
    _ = ((Fintype.card I : ℝ) * q) ^ K := by rw [mul_pow]

end LPPDifferentiability
