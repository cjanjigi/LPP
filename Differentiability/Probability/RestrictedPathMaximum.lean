/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Model.Animals.PathSets
public import LPP_Foundations.Model.Paths.Fintype
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import LPP_Foundations.Model.LastPassage.Basic
import LPP_Foundations.Model.Paths.Nonempty
import Mathlib.Algebra.Order.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic.Linarith

/-!
# Restricted Boolean path-count maximum

The finite, fixed-endpoint maximum used to bound the top-site count in `lem:tilt`.
The maximum is taken over actual paths that keep every vertex in the given
finite region; its count uses only the collected nonterminal sites.
-/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- A path with specified endpoints whose vertices, including its terminal vertex, lie in `R`. -/
abbrev PathInRegion (u : Lattice) (d : ℕ × ℕ) (R : Finset Lattice) :=
  {p : Path u d // ∀ j, p.vertex j ∈ R}

open Classical in
/-- The number of marked sites collected by the path. The terminal vertex is excluded. -/
noncomputable abbrev PathInRegion.countMarkedSites {u : Lattice} {d : ℕ × ℕ} {R : Finset Lattice}
    (p : PathInRegion u d R) (x : {z : Lattice // z ∈ R} → Bool) : ℕ :=
  (p.val.collectedSites.filter (fun z => if hz : z ∈ R then x ⟨z, hz⟩ = true else False)).card

open Classical in
/-- The maximum marked-site count over paths with the given endpoints inside `R`, as a real
number. The value is zero when there is no eligible path. -/
noncomputable abbrev restrictedPathMarkedCountMaximum (u : Lattice) (d : ℕ × ℕ) (R : Finset Lattice)
    (x : {z : Lattice // z ∈ R} → Bool) : ℝ :=
  (↑((Finset.univ : Finset (PathInRegion u d R)).sup (fun p => p.countMarkedSites x)) : ℝ)

open Classical in
private theorem restrictedPathCountMaximum_core (u : Lattice) (d : ℕ × ℕ)
    (R : Finset Lattice) :
    let F := restrictedPathMarkedCountMaximum u d R
    let extended : ({z : Lattice // z ∈ R} → Bool) → Environment := fun x z =>
      if hz : z ∈ R then if x ⟨z, hz⟩ then (1 : ℝ) else 0 else 0
    Measurable F ∧
      (∀ x, 0 ≤ F x) ∧
      (∀ x, F x ≤ (d.1 + d.2 : ℕ)) ∧
      (∀ x i b, |F (Function.update x i b) - F x| ≤ 1) ∧
      (∀ x b, 0 ≤ b →
        (F x > b ↔ ∃ p : PathInRegion u d R, b < (p.countMarkedSites x : ℝ))) ∧
      (∀ x, F x ≤ lastPassage (extended x) u d) := by
  classical
  let I : Type := {z : Lattice // z ∈ R}
  let Eligible := PathInRegion u d R
  let P : Finset Eligible := Finset.univ
  let count (p : Eligible) (x : I → Bool) := PathInRegion.countMarkedSites p x
  let F := restrictedPathMarkedCountMaximum u d R
  let extended : (I → Bool) → Environment := fun x z =>
    if hz : z ∈ R then if x ⟨z, hz⟩ then (1 : ℝ) else 0 else 0
  change Measurable F ∧
      (∀ x, 0 ≤ F x) ∧
      (∀ x, F x ≤ (d.1 + d.2 : ℕ)) ∧
      (∀ x i b, |F (Function.update x i b) - F x| ≤ 1) ∧
      (∀ x b, 0 ≤ b →
        (F x > b ↔ ∃ p : Eligible, b < (count p x : ℝ))) ∧
      (∀ x, F x ≤ lastPassage (extended x) u d)
  have hcollected_mem (p : Eligible) {z : Lattice}
      (hz : z ∈ p.val.collectedSites) : z ∈ R := by
    obtain ⟨j, rfl⟩ := (p.val.mem_collectedSites_iff z).mp hz
    exact p.property j.castSucc
  have hcount_le (p : Eligible) (x : I → Bool) :
      count p x ≤ d.1 + d.2 := by
    calc
      count p x ≤ p.val.collectedSites.card :=
        Finset.card_filter_le p.val.collectedSites _
      _ = d.1 + d.2 := p.val.collectedSites_card
  have hcount_update_le (p : Eligible) (x : I → Bool) (i : I) (b : Bool) :
      count p (Function.update x i b) ≤ count p x + 1 := by
    let A := p.val.collectedSites.filter
      (fun z => if hz : z ∈ R then x ⟨z, hz⟩ = true else False)
    let B := p.val.collectedSites.filter
      (fun z => if hz : z ∈ R then Function.update x i b ⟨z, hz⟩ = true else False)
    have hsubset : B ⊆ A ∪ ({i.1} : Finset Lattice) := by
      intro z hz
      obtain ⟨hzcol, hyfilter⟩ := Finset.mem_filter.mp hz
      have hzR := hcollected_mem p hzcol
      by_cases heq : (⟨z, hzR⟩ : I) = i
      · apply Finset.mem_union_right
        simp only [Finset.mem_singleton]
        exact congrArg Subtype.val heq
      · apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        refine ⟨hzcol, ?_⟩
        have hy : Function.update x i b ⟨z, hzR⟩ = true := by
          simpa [hzR] using hyfilter
        have hx : x ⟨z, hzR⟩ = true := by
          rw [Function.update_of_ne heq] at hy
          exact hy
        simpa [hzR] using hx
    have hcard : B.card ≤ A.card + 1 := by
      calc
        B.card ≤ (A ∪ ({i.1} : Finset Lattice)).card :=
          Finset.card_le_card hsubset
        _ ≤ A.card + ({i.1} : Finset Lattice).card :=
          Finset.card_union_le A ({i.1} : Finset Lattice)
        _ = A.card + 1 := by simp
    simpa [A, B, count, PathInRegion.countMarkedSites] using hcard
  have hupdate_back (x : I → Bool) (i : I) (b : Bool) :
      Function.update (Function.update x i b) i (x i) = x := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · rw [Function.update_of_ne hji, Function.update_of_ne hji]
  refine ⟨measurable_of_finite F, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change (0 : ℝ) ≤ (↑(P.sup (fun p => count p x)) : ℝ)
    exact_mod_cast (Nat.zero_le (P.sup (fun p => count p x)))
  · intro x
    have hsup : P.sup (fun p => count p x) ≤ d.1 + d.2 :=
      Finset.sup_le fun p _ => hcount_le p x
    change (↑(P.sup (fun p => count p x)) : ℝ) ≤
      (↑(d.1 + d.2 : ℕ) : ℝ)
    exact_mod_cast hsup
  · intro x i b
    have hsup_forward :
        P.sup (fun p => count p (Function.update x i b)) ≤
          P.sup (fun p => count p x) + 1 := by
      apply Finset.sup_le
      intro p hp
      calc
        count p (Function.update x i b) ≤ count p x + 1 := hcount_update_le p x i b
        _ ≤ P.sup (fun p => count p x) + 1 :=
          Nat.add_le_add_right
            (Finset.le_sup (f := fun q => count q x) hp) 1
    have hsup_backward :
        P.sup (fun p => count p x) ≤
          P.sup (fun p => count p (Function.update x i b)) + 1 := by
      apply Finset.sup_le
      intro p hp
      have h := hcount_update_le p (Function.update x i b) i (x i)
      have h' : count p x ≤ count p (Function.update x i b) + 1 := by
        simpa only [hupdate_back] using h
      calc
        count p x ≤ count p (Function.update x i b) + 1 := h'
        _ ≤ P.sup (fun p => count p (Function.update x i b)) + 1 :=
          Nat.add_le_add_right
            (Finset.le_sup (f := fun q => count q (Function.update x i b)) hp) 1
    have hforward :
        (↑(P.sup (fun p => count p (Function.update x i b))) : ℝ) ≤
          (↑(P.sup (fun p => count p x) : ℕ) : ℝ) + 1 := by
      exact_mod_cast hsup_forward
    have hbackward :
        (↑(P.sup (fun p => count p x) : ℕ) : ℝ) ≤
          (↑(P.sup (fun p => count p (Function.update x i b)) : ℕ) : ℝ) + 1 := by
      exact_mod_cast hsup_backward
    change |(↑(P.sup (fun p => count p (Function.update x i b)) : ℕ) : ℝ) -
      (↑(P.sup (fun p => count p x) : ℕ) : ℝ)| ≤ 1
    rw [abs_le]
    constructor <;> linarith
  · intro x b hb
    change (↑(P.sup (fun p => count p x)) : ℝ) > b ↔
      ∃ p : Eligible, b < (count p x : ℝ)
    constructor
    · intro hF
      have hP : P.Nonempty := by
        by_contra h
        have hEmpty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        have hzero : (↑(P.sup (fun p => count p x)) : ℝ) = 0 := by
          simp [hEmpty]
        rw [hzero] at hF
        exact (not_lt_of_ge hb) hF
      have himage :=
        Finset.sup_mem_of_nonempty (s := P) (f := fun p => count p x) hP
      change ∃ p ∈ P, count p x = P.sup (fun p => count p x) at himage
      obtain ⟨p, hp, hmax⟩ := himage
      refine ⟨p, ?_⟩
      rw [hmax]
      exact hF
    · rintro ⟨p, hp⟩
      have hmem : p ∈ P := Finset.mem_univ p
      have hle := Finset.le_sup (f := fun q => count q x) hmem
      exact hp.trans_le (by exact_mod_cast hle)
  · intro x
    have hpassage_nonneg : 0 ≤ lastPassage (extended x) u d := by
      obtain ⟨p⟩ := (pathNonempty u d)
      have hp : 0 ≤ pathWeight (extended x) p := by
        unfold pathWeight
        exact Finset.sum_nonneg fun j hj => by
          dsimp [extended]
          split_ifs <;> norm_num
      exact hp.trans (pathWeight_le_lastPassage (extended x) p)
    have hweight_count (p : Eligible) :
        pathWeight (extended x) p.val = (count p x : ℝ) := by
      have hsum :
          (∑ z ∈ p.val.collectedSites, extended x z) =
            ∑ z ∈ p.val.collectedSites,
              if (if hz : z ∈ R then x ⟨z, hz⟩ = true else False)
              then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        have hzR := hcollected_mem p hz
        cases hx : x ⟨z, hzR⟩ <;> simp [extended, hzR, hx]
      have hcard_sum :
          (count p x : ℝ) =
            ∑ z ∈ p.val.collectedSites,
              if (if hz : z ∈ R then x ⟨z, hz⟩ = true else False)
              then (1 : ℝ) else 0 := by
        change (PathInRegion.countMarkedSites p x : ℝ) = _
        rw [PathInRegion.countMarkedSites, Finset.card_filter]
        simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      calc
        pathWeight (extended x) p.val =
            ∑ z ∈ p.val.collectedSites, extended x z :=
          p.val.pathWeight_eq_sum_collectedSites (extended x)
        _ = _ := hsum
        _ = (count p x : ℝ) := hcard_sum.symm
    by_cases hP : P.Nonempty
    · have hcast :
          (↑(P.sup (fun p => count p x)) : ℝ) =
            P.sup' hP (fun p => (count p x : ℝ)) := by
        rw [← Finset.sup'_eq_sup hP]
        exact Nat.cast_finsetSup' (s := P) (f := fun p => count p x) hP
      have hle : P.sup' hP (fun p => (count p x : ℝ)) ≤
          lastPassage (extended x) u d := by
        apply Finset.sup'_le hP
        intro p hp
        rw [← hweight_count p]
        exact pathWeight_le_lastPassage (extended x) p.val
      change (↑(P.sup (fun p => count p x)) : ℝ) ≤
        lastPassage (extended x) u d
      exact hcast ▸ hle
    · have hEmpty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
      have hzero : (↑(P.sup (fun p => count p x)) : ℝ) = 0 := by
        simp [hEmpty]
      change (↑(P.sup (fun p => count p x)) : ℝ) ≤
        lastPassage (extended x) u d
      rw [hzero]
      exact hpassage_nonneg

/-- The maximum count is measurable on the finite space of Boolean marks. -/
theorem restrictedPathCountMaximum_measurable (u : Lattice) (d : ℕ × ℕ)
    (R : Finset Lattice) : Measurable (restrictedPathMarkedCountMaximum u d R) :=
  (restrictedPathCountMaximum_core u d R).1

/-- The maximum count is nonnegative, including when there are no eligible paths. -/
theorem restrictedPathCountMaximum_nonneg (u : Lattice) (d : ℕ × ℕ)
    (R : Finset Lattice) : ∀ x, 0 ≤ restrictedPathMarkedCountMaximum u d R x :=
  (restrictedPathCountMaximum_core u d R).2.1

/-- The maximum is at most the common length of the paths. -/
theorem restrictedPathCountMaximum_le_length (u : Lattice) (d : ℕ × ℕ)
    (R : Finset Lattice) : ∀ x, restrictedPathMarkedCountMaximum u d R x ≤ (d.1 + d.2 : ℕ) :=
  (restrictedPathCountMaximum_core u d R).2.2.1

open Classical in
/-- Flipping a site's mark changes the maximum count by at most one. -/
theorem restrictedPathCountMaximum_update_abs_le (u : Lattice) (d : ℕ × ℕ)
    (R : Finset Lattice) :
    let F := restrictedPathMarkedCountMaximum u d R
    ∀ x i b, |F (Function.update x i b) - F x| ≤ 1 :=
  (restrictedPathCountMaximum_core u d R).2.2.2.1

/-- A nonnegative threshold is exceeded exactly when some path in the region exceeds it. -/
theorem restrictedPathCountMaximum_gt_iff (u : Lattice) (d : ℕ × ℕ)
    (R : Finset Lattice) :
    ∀ x b, 0 ≤ b →
      (restrictedPathMarkedCountMaximum u d R x > b ↔
        ∃ p : PathInRegion u d R, b < (p.countMarkedSites x : ℝ)) :=
  (restrictedPathCountMaximum_core u d R).2.2.2.2.1

open Classical in
/-- Extending the Boolean weights by zero outside the region makes the unrestricted last-passage
value at least the restricted maximum count. -/
theorem restrictedPathCountMaximum_le_lastPassage (u : Lattice) (d : ℕ × ℕ)
    (R : Finset Lattice) :
    let extended : ({z : Lattice // z ∈ R} → Bool) → Environment := fun x z =>
      if hz : z ∈ R then if x ⟨z, hz⟩ then (1 : ℝ) else 0 else 0
    ∀ x, restrictedPathMarkedCountMaximum u d R x ≤ lastPassage (extended x) u d :=
  (restrictedPathCountMaximum_core u d R).2.2.2.2.2

end LPPDifferentiability
