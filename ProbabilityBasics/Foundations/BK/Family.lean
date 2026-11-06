/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Foundations.BK.Witness
public import ProbabilityBasics.Foundations.BK.WitnessMeasurable
public import ProbabilityBasics.Foundations.BK.Finite
public import Mathlib.Data.Finset.Union
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# The BK inequality for a finite family, finitely many coordinates

This file carries out the "repeated application of Theorem (3.3)" in the proof of (3.11) of van den
Berg and Kesten (1985). It goes beyond the paper in generality: the coordinates lie in general
ordered spaces, and the paper's associativity of `∘` is replaced by an inclusion.

The disjoint occurrence `disjointOccurrenceOn s A` of the events `A j` with `j ∈ s` is defined in
`WitnessMeasurable.lean`. This file proves:

* `disjointOccurrenceOn_univ`: for `s = univ` it is `disjointOccurrence A`.
* `disjointOccurrenceOn_empty`: for `s = ∅` it is every configuration.
* `isUpperSet_disjointOccurrenceOn`: it is increasing when every `A j`, `j ∈ s`, is.
* `disjointOccurrenceOn_insert_subset`: the insertion step, as an inclusion into a box occurrence.
* `bk_inequality_family_pi`: the statement of `bk_inequality_family`. It follows by
  induction over `s` from `bk_inequality_pi`, measurability of the disjoint occurrence and
  `Finset.prod_insert`.

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985), (3.11) and Theorem 3.3.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityBasics.BK

section Combinatorics

variable {ι : Type*} {E : ι → Type*} {J : Type*}

/-- For `s` the whole finite index set, the disjoint occurrence on `s` is the disjoint occurrence of
the whole family (the family `E_1, ..., E_k` of (3.11) of van den Berg and Kesten (1985)). -/
theorem disjointOccurrenceOn_univ [Fintype J] (A : J → Set (∀ i, E i)) :
    disjointOccurrenceOn (Finset.univ : Finset J) A = disjointOccurrence A := by
  ext ω
  constructor
  · rintro ⟨K, hK, hW⟩
    exact ⟨K, fun j l hjl => hK j (Finset.mem_univ j) l (Finset.mem_univ l) hjl,
      fun j => hW j (Finset.mem_univ j)⟩
  · rintro ⟨K, hK, hW⟩
    exact ⟨K, fun j _ l _ hjl => hK hjl, fun j _ => hW j⟩

/-- The disjoint occurrence on the empty set of indices is every configuration: no witness is
required (the start of the induction behind (3.11)). -/
theorem disjointOccurrenceOn_empty (A : J → Set (∀ i, E i)) :
    disjointOccurrenceOn (∅ : Finset J) A = (Set.univ : Set (∀ i, E i)) := by
  ext ω
  exact ⟨fun _ => trivial, fun _ => ⟨fun _ => ∅, by simp, by simp⟩⟩

/-- The disjoint occurrence on `s` of increasing events is increasing: moving the configuration up
keeps every witness set (`isWitnessSet_of_le`), with the same family of coordinate sets (not in the
paper). -/
theorem isUpperSet_disjointOccurrenceOn [∀ i, Preorder (E i)] (s : Finset J)
    {A : J → Set (∀ i, E i)} (hA : ∀ j ∈ s, IsUpperSet (A j)) :
    IsUpperSet (disjointOccurrenceOn s A) := by
  intro ω ω' hle hω
  obtain ⟨K, hK, hW⟩ := hω
  exact ⟨K, hK, fun j hj => isWitnessSet_of_le (hA j hj) hle (hW j hj)⟩

/-- The insertion step. A disjoint occurrence on `insert j s` is a box occurrence of `A j` and the
disjoint occurrence on `s`, when `j ∉ s`. Given a family `K` of witness sets, the box occurrence
uses `K j` for `A j` and `s.biUnion K` for the other events. This is an inclusion, not the equality
that the paper obtains from the associativity of `∘` ((3.11) of van den Berg and Kesten (1985)). -/
theorem disjointOccurrenceOn_insert_subset [DecidableEq J] {s : Finset J} {j : J} (hj : j ∉ s)
    (A : J → Set (∀ i, E i)) :
    disjointOccurrenceOn (insert j s) A ⊆ boxOccurrence (A j) (disjointOccurrenceOn s A) := by
  classical
  rintro ω ⟨K, hK, hW⟩
  -- `K j` is disjoint from every `K l` with `l ∈ s`, since `l ≠ j`.
  have hdisj : ∀ l ∈ s, Disjoint (K j) (K l) := fun l hl =>
    hK j (Finset.mem_insert_self j s) l (Finset.mem_insert_of_mem hl)
      (fun h => hj (by rw [h]; exact hl))
  refine ⟨K j, s.biUnion K, (Finset.disjoint_biUnion_right _ _ _).2 hdisj,
    hW j (Finset.mem_insert_self j s), ?_⟩
  -- Every `η` that agrees with `ω` on `s.biUnion K` keeps the same family `K` witnessing on `s`.
  intro η hη
  refine ⟨K, fun l hl l' hl' hll' => hK l (Finset.mem_insert_of_mem hl) l'
    (Finset.mem_insert_of_mem hl') hll', fun l hl => ?_⟩
  intro ζ hζ
  refine hW l (Finset.mem_insert_of_mem hl) ?_
  intro i hi
  rw [hζ i hi]
  exact hη i (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨l, hl, Finset.mem_coe.1 hi⟩))

end Combinatorics

section Inequality

variable {ι : Type*} {E : ι → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
  (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- **BK inequality for a finite family, finitely many coordinates** (the statement of
`bk_inequality_family`). This is (3.11) of van den Berg and Kesten (1985), whose proof is
"repeated application of Theorem (3.3)". The claim `P[disjointOccurrenceOn s A] ≤ ∏ j ∈ s, P[A j]`
is proved by induction over `s`: the empty case is `P[univ] = 1`, and the insertion step combines
`disjointOccurrenceOn_insert_subset`, `bk_inequality_pi` (with measurability and increase of the
disjoint occurrence on `s`) and `Finset.prod_insert`. Beyond the paper in generality. -/
theorem bk_inequality_family_pi [Fintype ι] {J : Type*} [Fintype J]
    {A : J → Set (∀ i, E i)}
    (hAm : ∀ j, MeasurableSet (A j)) (hA : ∀ j, IsUpperSet (A j)) :
    Measure.pi μ (disjointOccurrence A) ≤ ∏ j, Measure.pi μ (A j) := by
  classical
  have key : ∀ s : Finset J,
      Measure.pi μ (disjointOccurrenceOn s A) ≤ ∏ j ∈ s, Measure.pi μ (A j) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [disjointOccurrenceOn_empty, Finset.prod_empty]
      exact measure_univ.le
    | insert j s hj ih =>
      rw [Finset.prod_insert hj]
      calc Measure.pi μ (disjointOccurrenceOn (insert j s) A)
          ≤ Measure.pi μ (boxOccurrence (A j) (disjointOccurrenceOn s A)) :=
            measure_mono (disjointOccurrenceOn_insert_subset hj A)
        _ ≤ Measure.pi μ (A j) * Measure.pi μ (disjointOccurrenceOn s A) :=
            bk_inequality_pi μ (hAm j)
              (measurableSet_disjointOccurrenceOn s (fun l _ => hAm l) (fun l _ => hA l))
              (hA j) (isUpperSet_disjointOccurrenceOn s fun l _ => hA l)
        _ ≤ Measure.pi μ (A j) * ∏ l ∈ s, Measure.pi μ (A l) := by gcongr
  have hfull := key Finset.univ
  rwa [disjointOccurrenceOn_univ] at hfull

end Inequality

end ProbabilityBasics.BK
