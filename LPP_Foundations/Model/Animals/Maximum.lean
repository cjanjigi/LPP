/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.Family
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

/-! The maximum weight among rooted lattice animals of positive size. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- The sum of a real site field over a finite set of lattice sites. -/
def animalWeight (w : Lattice → ℝ) (s : Finset Lattice) : ℝ :=
  ∑ v ∈ s, w v

/-- The maximum weight over exactly the rooted, connected animals of size `n`.
There is no value at size zero, when the family is empty. -/
noncomputable def animalMaximum (n : ℕ) (hn : 1 ≤ n) (w : Lattice → ℝ) : ℝ :=
  (animalFamily_finite n).toFinset.sup'
    ((animalFamily_finite n).toFinset_nonempty.mpr (animalFamily_nonempty n hn))
    (fun s => animalWeight w s)

/-- The positivity proof used to define the maximum does not affect its value. -/
theorem animalMaximum_proof_irrel (n : ℕ) (hn₁ hn₂ : 1 ≤ n) (w : Lattice → ℝ) :
    animalMaximum n hn₁ w = animalMaximum n hn₂ w := by
  cases Subsingleton.elim hn₁ hn₂
  rfl

/-- Every animal's weight is at most the maximum. -/
theorem animalWeight_le_animalMaximum (n : ℕ) (hn : 1 ≤ n) (w : Lattice → ℝ)
    {s : Finset Lattice} (hs : s ∈ animalFamily n) :
    animalWeight w s ≤ animalMaximum n hn w := by
  classical
  have hs' : s ∈ (animalFamily_finite n).toFinset :=
    (animalFamily_finite n).mem_toFinset.mpr hs
  exact Finset.le_sup' (f := fun t => animalWeight w t) hs'

/-- Some rooted animal attains the finite maximum. -/
theorem exists_animalWeight_eq_animalMaximum (n : ℕ) (hn : 1 ≤ n)
    (w : Lattice → ℝ) :
    ∃ s ∈ animalFamily n, animalWeight w s = animalMaximum n hn w := by
  classical
  let F := (animalFamily_finite n).toFinset
  have hF : F.Nonempty :=
    (animalFamily_finite n).toFinset_nonempty.mpr (animalFamily_nonempty n hn)
  obtain ⟨s, hs, hsup⟩ :=
    Finset.exists_mem_eq_sup' hF (fun t => animalWeight w t)
  refine ⟨s, (animalFamily_finite n).mem_toFinset.mp ?_, ?_⟩
  · change s ∈ F
    exact hs
  · change animalWeight w s = F.sup' hF (fun t => animalWeight w t)
    exact hsup.symm

/-- The maximum is at most a bound exactly when every animal sum is. -/
theorem animalMaximum_le_iff (n : ℕ) (hn : 1 ≤ n) (w : Lattice → ℝ) (u : ℝ) :
    animalMaximum n hn w ≤ u ↔
      ∀ s ∈ animalFamily n, animalWeight w s ≤ u := by
  classical
  let F := (animalFamily_finite n).toFinset
  have hF : F.Nonempty :=
    (animalFamily_finite n).toFinset_nonempty.mpr (animalFamily_nonempty n hn)
  change F.sup' hF (fun s => animalWeight w s) ≤ u ↔
    ∀ s ∈ animalFamily n, animalWeight w s ≤ u
  rw [Finset.sup'_le_iff]
  constructor
  · intro h s hs
    exact h s ((animalFamily_finite n).mem_toFinset.mpr hs)
  · intro h s hs
    exact h s ((animalFamily_finite n).mem_toFinset.mp hs)

/-- A threshold is below the maximum exactly when some animal reaches it. -/
theorem le_animalMaximum_iff_exists_animalWeight_ge
    (n : ℕ) (hn : 1 ≤ n) (w : Lattice → ℝ) (t : ℝ) :
    t ≤ animalMaximum n hn w ↔
      ∃ s ∈ animalFamily n, t ≤ animalWeight w s := by
  classical
  let F := (animalFamily_finite n).toFinset
  have hF : F.Nonempty :=
    (animalFamily_finite n).toFinset_nonempty.mpr (animalFamily_nonempty n hn)
  change t ≤ F.sup' hF (fun s => animalWeight w s) ↔
    ∃ s ∈ animalFamily n, t ≤ animalWeight w s
  rw [Finset.le_sup'_iff]
  constructor
  · rintro ⟨s, hs, ht⟩
    exact ⟨s, (animalFamily_finite n).mem_toFinset.mp hs, ht⟩
  · rintro ⟨s, hs, ht⟩
    exact ⟨s, (animalFamily_finite n).mem_toFinset.mpr hs, ht⟩

/-- Equality with `x` means that `x` is an upper bound attained by some animal.
This characterizes the value without reference to the finite enumeration. -/
theorem animalMaximum_eq_iff (n : ℕ) (hn : 1 ≤ n) (w : Lattice → ℝ) (x : ℝ) :
    animalMaximum n hn w = x ↔
      (∀ s ∈ animalFamily n, animalWeight w s ≤ x) ∧
        ∃ s ∈ animalFamily n, animalWeight w s = x := by
  constructor
  · intro hx
    constructor
    · intro s hs
      simpa [hx] using animalWeight_le_animalMaximum n hn w hs
    · obtain ⟨s, hs, hmax⟩ := exists_animalWeight_eq_animalMaximum n hn w
      exact ⟨s, hs, by simpa [hx] using hmax⟩
  · rintro ⟨hupper, ⟨s, hs, hvalue⟩⟩
    apply le_antisymm
    · exact (animalMaximum_le_iff n hn w x).2 hupper
    · rw [← hvalue]
      exact animalWeight_le_animalMaximum n hn w hs

private theorem animalFamily_one_member_eq_singleton {s : Finset Lattice}
    (hs : s ∈ animalFamily 1) : s = {0} := by
  obtain ⟨_, hzero, hcard⟩ := (mem_animalFamily_iff 1 s).mp hs
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
  have hz0 : z = 0 := by
    have hmem : (0 : Lattice) ∈ ({z} : Finset Lattice) := by
      simpa [hz] using hzero
    exact (Finset.mem_singleton.mp hmem).symm
  simp [hz, hz0]

/-- For size one, the only animal is the origin, for signed fields too. -/
theorem animalMaximum_one (w : Lattice → ℝ) :
    animalMaximum 1 (by norm_num) w = w 0 := by
  apply (animalMaximum_eq_iff 1 (by norm_num) w (w 0)).2
  constructor
  · intro s hs
    rw [animalFamily_one_member_eq_singleton hs]
    simp [animalWeight]
  · obtain ⟨s, hs⟩ := animalFamily_nonempty 1 (by norm_num)
    exact ⟨s, hs, by
      rw [animalFamily_one_member_eq_singleton hs]
      simp [animalWeight]⟩

/-- Pointwise nonnegative site weights give a nonnegative animal maximum. -/
theorem animalMaximum_nonneg_of_forall_nonneg (n : ℕ) (hn : 1 ≤ n)
    (w : Lattice → ℝ) (hw : ∀ v, 0 ≤ w v) :
    0 ≤ animalMaximum n hn w := by
  obtain ⟨s, hs, hmax⟩ := exists_animalWeight_eq_animalMaximum n hn w
  rw [← hmax]
  exact Finset.sum_nonneg (fun v hv => hw v)

/-- A pointwise site upper bound gives the size-times-bound maximum estimate. -/
theorem animalMaximum_le_mul_of_forall_le (n : ℕ) (hn : 1 ≤ n)
    (w : Lattice → ℝ) (L : ℝ) (hw : ∀ v, w v ≤ L) :
    animalMaximum n hn w ≤ (n : ℝ) * L := by
  apply (animalMaximum_le_iff n hn w _).2
  intro s hs
  obtain ⟨_, _, hcard⟩ := (mem_animalFamily_iff n s).mp hs
  calc
    animalWeight w s = ∑ v ∈ s, w v := rfl
    _ ≤ ∑ v ∈ s, L := Finset.sum_le_sum (fun v hv => hw v)
    _ = (s.card : ℝ) * L := by simp
    _ = (n : ℝ) * L := by rw [hcard]

end LPPDifferentiability
