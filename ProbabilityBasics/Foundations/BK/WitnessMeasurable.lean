/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Foundations.BK.Witness
public import ProbabilityBasics.Foundations.BK.Levels
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of disjoint occurrence with finitely many coordinates

This goes beyond van den Berg and Kesten (1985). The paper works on `{0,1}^n` (or on `ℕ^n`) where
every set is measurable, and it remarks (p. 556) that on `R₊^n` the sets `A + B` are only
universally measurable. Here the coordinates lie in general ordered spaces, so measurability of
`A □ B` has to be proved.

Let `ι` be a finite type and let each `E i` be a linear order with the order topology, a countable
base and the Borel `σ`-algebra.

* `measurableSet_isWitnessSet`: for a measurable increasing event `A` and a finite set `K` of
  coordinates, the set of configurations at which `K` witnesses `A` is measurable. It is the
  intersection, over all ways `n : ι → ℕ` of choosing a point `c i (n i)` of a countable coinitial
  set in every coordinate off `K`, of the events "`ω` on `K` and `c i (n i)` off `K` lies in `A`".
* `measurableSet_boxOccurrence`: the disjoint occurrence `A □ B` of two measurable increasing
  events is measurable.
* `disjointOccurrenceOn s A`: disjoint occurrence of the events `A j` with `j ∈ s` only. It is
  defined here because this module needs it; `disjointOccurrenceOn_univ` and the insertion step
  belong to the family module.
* `measurableSet_disjointOccurrenceOn` and `measurableSet_disjointOccurrence`: the same for a finite
  family of measurable increasing events.

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985).
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityBasics.BK

variable {ι : Type*} {E : ι → Type*}

/-- Disjoint occurrence of the events `A j` with `j ∈ s` only: there are finite sets `K j` of
coordinates, pairwise disjoint for the indices in `s`, such that `K j` witnesses `A j` at `ω` for
every `j ∈ s`. For `s` the whole index set this is `disjointOccurrence A`; for `s = ∅` it is every
configuration (not in the paper). -/
def disjointOccurrenceOn {J : Type*} (s : Finset J) (A : J → Set (∀ i, E i)) :
    Set (∀ i, E i) :=
  {ω | ∃ K : J → Finset ι, (∀ j ∈ s, ∀ l ∈ s, j ≠ l → Disjoint (K j) (K l)) ∧
    ∀ j ∈ s, IsWitnessSet (A j) (K j : Set ι) ω}

section Measurability

variable [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]

/-- A nonempty ordered space of the class considered here has a sequence such that every point lies
above some term of it. The sequence enumerates the countable coinitial set of a level set (of the
zero measure, since no law is involved here). -/
private theorem exists_coinitial_seq {X : Type*} [MeasurableSpace X] [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [SecondCountableTopology X] [BorelSpace X] (x₀ : X) :
    ∃ c : ℕ → X, ∀ x, ∃ n, c n ≤ x := by
  obtain ⟨D, hD⟩ := exists_isLevelSet (0 : Measure X)
  obtain ⟨d₀, hd₀, -⟩ := hD.coinitial x₀
  obtain ⟨c, hc⟩ := hD.countable.exists_eq_range ⟨d₀, hd₀⟩
  refine ⟨c, fun x => ?_⟩
  obtain ⟨d, hd, hdx⟩ := hD.coinitial x
  have hdc : d ∈ Set.range c := hc ▸ hd
  obtain ⟨n, rfl⟩ := hdc
  exact ⟨n, hdx⟩

/-- For a measurable increasing event `A` and a finite set `K` of coordinates, the set of
configurations at which `K` witnesses `A` is measurable. It is the countable intersection over
`n : ι → ℕ` of the events `{ω | K.piecewise ω (fun i => c i (n i)) ∈ A}`, where `c i` enumerates a
coinitial set in coordinate `i` (not in the paper). -/
theorem measurableSet_isWitnessSet [Fintype ι] {A : Set (∀ i, E i)}
    (hAm : MeasurableSet A) (hA : IsUpperSet A) (K : Finset ι) :
    MeasurableSet {ω | IsWitnessSet A (K : Set ι) ω} := by
  classical
  by_cases hne : Nonempty (∀ i, E i)
  swap
  · have hemp : IsEmpty (∀ i, E i) := not_nonempty_iff.1 hne
    rw [Set.eq_empty_of_isEmpty {ω : ∀ i, E i | IsWitnessSet A (K : Set ι) ω}]
    exact MeasurableSet.empty
  obtain ⟨x₀⟩ := hne
  choose c hc using fun i => exists_coinitial_seq (x₀ i)
  -- `pad n ω` is `ω` on `K` and `c i (n i)` off `K`.
  let pad : (ι → ℕ) → (∀ i, E i) → ∀ i, E i := fun n ω i => if i ∈ K then ω i else c i (n i)
  have hpad : ∀ n, Measurable (pad n) := by
    intro n
    refine measurable_pi_iff.2 fun i => ?_
    by_cases hi : i ∈ K
    · simpa [pad, hi] using measurable_pi_apply i
    · simp [pad, hi]
  have hset : {ω | IsWitnessSet A (K : Set ι) ω} = ⋂ n : ι → ℕ, pad n ⁻¹' A := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage]
    constructor
    · -- `pad n ω` agrees with `ω` on `K`, so it is in the cylinder, which is inside `A`.
      intro hK n
      have hK' : agreementCylinder (K : Set ι) ω ⊆ A := hK
      refine hK' ?_
      show ∀ i ∈ (K : Set ι), pad n ω i = ω i
      intro i hi
      exact ite_eq_left (Finset.mem_coe.1 hi)
    · -- Every `η` in the cylinder lies above some `pad n ω`, and `A` is increasing.
      intro h
      show agreementCylinder (K : Set ι) ω ⊆ A
      intro η hη
      choose n hn using fun i => hc i (η i)
      have hle : pad n ω ≤ η := by
        intro i
        by_cases hi : i ∈ K
        · show (if i ∈ K then ω i else c i (n i)) ≤ η i
          rw [ite_eq_left hi]
          exact le_of_eq (hη i (Finset.mem_coe.2 hi)).symm
        · show (if i ∈ K then ω i else c i (n i)) ≤ η i
          rw [ite_eq_right hi]
          exact hn i
      exact hA hle (h n)
  rw [hset]
  exact MeasurableSet.iInter fun n => hpad n hAm

/-- The configurations at which some family `K : J → Finset ι` with a property `P` (which does not
depend on the configuration) has `K j` witnessing `A j` for every `j`, form a measurable set when
`J` is finite and every `A j` is measurable and increasing. The union runs over a countable set of
families. -/
private theorem measurableSet_witnessFamily [Fintype ι] {J : Type*} [Finite J]
    {A : J → Set (∀ i, E i)} (hAm : ∀ j, MeasurableSet (A j)) (hA : ∀ j, IsUpperSet (A j))
    (P : (J → Finset ι) → Prop) :
    MeasurableSet {ω | ∃ K : J → Finset ι, P K ∧ ∀ j, IsWitnessSet (A j) (K j : Set ι) ω} := by
  have hset : {ω | ∃ K : J → Finset ι, P K ∧ ∀ j, IsWitnessSet (A j) (K j : Set ι) ω} =
      ⋃ K : J → Finset ι, ⋃ _ : P K, ⋂ j, {ω | IsWitnessSet (A j) (K j : Set ι) ω} := by
    ext ω
    constructor
    · rintro ⟨K, hK, hW⟩
      exact mem_iUnion.2 ⟨K, mem_iUnion.2 ⟨hK, mem_iInter.2 fun j => hW j⟩⟩
    · intro h
      obtain ⟨K, h⟩ := mem_iUnion.1 h
      obtain ⟨hK, h⟩ := mem_iUnion.1 h
      exact ⟨K, hK, fun j => mem_iInter.1 h j⟩
  rw [hset]
  exact MeasurableSet.iUnion fun K => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iInter fun j => measurableSet_isWitnessSet (hAm j) (hA j) (K j)

/-- For finitely many coordinates, the disjoint occurrence of two measurable increasing events is
measurable. It is the union over the countably many pairs `(K, L)` of disjoint finite sets of
coordinates of the intersection of the two witness events. This is not in the paper, which treats
only sets on which measurability is automatic. -/
theorem measurableSet_boxOccurrence [Fintype ι] {A B : Set (∀ i, E i)}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    MeasurableSet (boxOccurrence A B) := by
  have hset : boxOccurrence A B = ⋃ K : Finset ι, ⋃ L : Finset ι, ⋃ _ : Disjoint K L,
      {ω | IsWitnessSet A (K : Set ι) ω} ∩ {ω | IsWitnessSet B (L : Set ι) ω} := by
    ext ω
    constructor
    · rintro ⟨K, L, hKL, hK, hL⟩
      exact mem_iUnion.2 ⟨K, mem_iUnion.2 ⟨L, mem_iUnion.2 ⟨hKL, ⟨hK, hL⟩⟩⟩⟩
    · intro h
      obtain ⟨K, h⟩ := mem_iUnion.1 h
      obtain ⟨L, h⟩ := mem_iUnion.1 h
      obtain ⟨hKL, hK, hL⟩ := mem_iUnion.1 h
      exact ⟨K, L, hKL, hK, hL⟩
  rw [hset]
  exact MeasurableSet.iUnion fun K => MeasurableSet.iUnion fun L => MeasurableSet.iUnion fun _ =>
    (measurableSet_isWitnessSet hAm hA K).inter (measurableSet_isWitnessSet hBm hB L)

/-- For finitely many coordinates, the disjoint occurrence of a finite family of measurable
increasing events is measurable (not in the paper). -/
theorem measurableSet_disjointOccurrence [Fintype ι] {J : Type*} [Finite J]
    {A : J → Set (∀ i, E i)}
    (hAm : ∀ j, MeasurableSet (A j)) (hA : ∀ j, IsUpperSet (A j)) :
    MeasurableSet (disjointOccurrence A) :=
  measurableSet_witnessFamily hAm hA (fun K => Pairwise fun j l => Disjoint (K j) (K l))

/-- For finitely many coordinates, the disjoint occurrence on a finite set `s` of indices of
measurable increasing events is measurable. Only the events with index in `s` are required to be
measurable and increasing. A family of witness sets indexed by `↥s` is extended by the empty set
off `s`, so the statement reduces to the finite case (not in the paper). -/
theorem measurableSet_disjointOccurrenceOn [Fintype ι] {J : Type*} (s : Finset J)
    {A : J → Set (∀ i, E i)}
    (hAm : ∀ j ∈ s, MeasurableSet (A j)) (hA : ∀ j ∈ s, IsUpperSet (A j)) :
    MeasurableSet (disjointOccurrenceOn s A) := by
  classical
  have hfam := measurableSet_witnessFamily (ι := ι) (J := ↥s) (A := fun j : s => A j)
    (fun j => hAm j j.2) (fun j => hA j j.2)
    (fun K => ∀ j l : s, j ≠ l → Disjoint (K j) (K l))
  have hset : disjointOccurrenceOn s A = {ω | ∃ K : s → Finset ι,
      (∀ j l : s, j ≠ l → Disjoint (K j) (K l)) ∧
        ∀ j : s, IsWitnessSet (A j) (K j : Set ι) ω} := by
    ext ω
    constructor
    · -- Restrict the family to `s`.
      rintro ⟨K, hK, hW⟩
      exact ⟨fun j => K j, fun j l hjl => hK (j : J) j.2 (l : J) l.2 (fun h => hjl (Subtype.ext h)),
        fun j => hW (j : J) j.2⟩
    · -- Extend the family by the empty set off `s`.
      rintro ⟨K, hK, hW⟩
      have hext : ∀ j (hj : j ∈ s), (if h : j ∈ s then K ⟨j, h⟩ else ∅) = K ⟨j, hj⟩ :=
        fun j hj => by simp [hj]
      refine ⟨fun j => if h : j ∈ s then K ⟨j, h⟩ else ∅, ?_, ?_⟩
      · intro j hj l hl hjl
        show Disjoint (if h : j ∈ s then K ⟨j, h⟩ else ∅) (if h : l ∈ s then K ⟨l, h⟩ else ∅)
        rw [hext j hj, hext l hl]
        exact hK ⟨j, hj⟩ ⟨l, hl⟩ (fun h => hjl (congrArg Subtype.val h))
      · intro j hj
        show IsWitnessSet (A j) ((if h : j ∈ s then K ⟨j, h⟩ else ∅ : Finset ι) : Set ι) ω
        rw [hext j hj]
        exact hW ⟨j, hj⟩
  rw [hset]
  exact hfam

end Measurability

end ProbabilityBasics.BK
