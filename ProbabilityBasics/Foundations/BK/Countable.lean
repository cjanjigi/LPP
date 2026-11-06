/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Foundations.BK.MergeProduct
public import ProbabilityBasics.Foundations.BK.Finite
public import ProbabilityBasics.Foundations.BK.Family
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Logic.Equiv.List

/-!
# The BK inequality for countably many coordinates

This file proves an extension of the finite-coordinate BK inequality to product laws on
countably many coordinates. In the proof of (3.11), van den Berg and Kesten use a finite-region
limit before reducing to finite W and applying Theorem 3.3.

## Main results

* `bk_inequality_infinitePi_impl`: for a countable index type and measurable increasing events `A`
  and `B`, `P[A □ B] ≤ P[A] P[B]` for the infinite product law (outer measure on the left, since
  `A □ B` need not be measurable). This is the statement of `bk_inequality_infinitePi`.
* `bk_inequality_family_infinitePi_impl`: the same for a finite family of events, with the product
  on the right. This is the statement of `bk_inequality_family_infinitePi`.

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985), 556-569.

## Proof outline

Fix a finite set `F` of coordinates. If disjoint witness sets `K, L ⊆ F` witness `A` and `B` at `ω`,
then the traces of `K` and `L` on `F` witness `sureOn μ F A` and `sureOn μ F B` at the restriction
of `ω` to `F`: fixing the coordinates of `K` forces `A` whatever the other coordinates are. So the
event "both witnesses lie in `F`" is inside the preimage, under the restriction to `F`, of the box
occurrence of the two `sureOn` events. Its probability is at most the finite product law of that box
occurrence (`Measure.le_map_apply`, `Measure.infinitePi_map_restrict`), then at most the product of
the finite laws of the two `sureOn` events (`bk_inequality_pi`), then at most `P[A] P[B]`
(`pi_sureOn_le_infinitePi`). Finally `A □ B` is the union over `F` of these events. The union is
directed over the countable type `Finset ι`, and `Directed.measure_iUnion` holds for arbitrary sets,
so `P[A □ B]` is the supremum of their probabilities. The family version is identical, with
`bk_inequality_family_pi` and a product of inequalities.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityBasics.BK

section Within

variable {ι : Type*} {E : ι → Type*}

/-- The disjoint occurrence of `A` and `B` with both witness sets inside the finite set `F` of
coordinates. -/
private def boxOccurrenceWithin (F : Finset ι) (A B : Set (∀ i, E i)) : Set (∀ i, E i) :=
  {ω | ∃ K L : Finset ι, K ⊆ F ∧ L ⊆ F ∧ Disjoint K L ∧
    IsWitnessSet A (K : Set ι) ω ∧ IsWitnessSet B (L : Set ι) ω}

/-- The disjoint occurrence of a family of events with all witness sets inside the finite set `F`
of coordinates. -/
private def disjointOccurrenceWithin {J : Type*} (F : Finset ι) (A : J → Set (∀ i, E i)) :
    Set (∀ i, E i) :=
  {ω | ∃ K : J → Finset ι, (∀ j, K j ⊆ F) ∧ Pairwise (fun j l => Disjoint (K j) (K l)) ∧
    ∀ j, IsWitnessSet (A j) (K j : Set ι) ω}

/-- A larger set of coordinates allows more witnesses. -/
private theorem boxOccurrenceWithin_mono {F G : Finset ι} (h : F ⊆ G) (A B : Set (∀ i, E i)) :
    boxOccurrenceWithin F A B ⊆ boxOccurrenceWithin G A B := by
  rintro ω ⟨K, L, hK, hL, hKL, hKw, hLw⟩
  exact ⟨K, L, hK.trans h, hL.trans h, hKL, hKw, hLw⟩

/-- `A □ B` is the union over the finite sets `F` of the events with both witnesses inside `F`:
take `F = K ∪ L`. -/
private theorem iUnion_boxOccurrenceWithin (A B : Set (∀ i, E i)) :
    ⋃ F : Finset ι, boxOccurrenceWithin F A B = boxOccurrence A B := by
  classical
  ext ω
  simp only [mem_iUnion]
  constructor
  · rintro ⟨F, K, L, -, -, hKL, hK, hL⟩
    exact ⟨K, L, hKL, hK, hL⟩
  · rintro ⟨K, L, hKL, hK, hL⟩
    exact ⟨K ∪ L, K, L, Finset.subset_union_left, Finset.subset_union_right, hKL, hK, hL⟩

/-- The events with both witnesses inside `F` form a directed family over `Finset ι`: use
`F ∪ G`. -/
private theorem directed_boxOccurrenceWithin (A B : Set (∀ i, E i)) :
    Directed (· ⊆ ·) (fun F : Finset ι => boxOccurrenceWithin F A B) := by
  classical
  intro F G
  exact ⟨F ∪ G, boxOccurrenceWithin_mono Finset.subset_union_left A B,
    boxOccurrenceWithin_mono Finset.subset_union_right A B⟩

/-- Family version of `boxOccurrenceWithin_mono`. -/
private theorem disjointOccurrenceWithin_mono {J : Type*} {F G : Finset ι} (h : F ⊆ G)
    (A : J → Set (∀ i, E i)) : disjointOccurrenceWithin F A ⊆ disjointOccurrenceWithin G A := by
  rintro ω ⟨K, hK, hKL, hW⟩
  exact ⟨K, fun j => (hK j).trans h, hKL, hW⟩

/-- `disjointOccurrence A` is the union over the finite sets `F` of the events with all witnesses
inside `F`: take `F` the union of the witness sets of the finitely many events. -/
private theorem iUnion_disjointOccurrenceWithin {J : Type*} [Fintype J] (A : J → Set (∀ i, E i)) :
    ⋃ F : Finset ι, disjointOccurrenceWithin F A = disjointOccurrence A := by
  classical
  ext ω
  simp only [mem_iUnion]
  constructor
  · rintro ⟨F, K, -, hKL, hW⟩
    exact ⟨K, hKL, hW⟩
  · rintro ⟨K, hKL, hW⟩
    exact ⟨Finset.univ.sup K, K, fun j => Finset.le_sup (f := K) (Finset.mem_univ j), hKL, hW⟩

/-- Family version of `directed_boxOccurrenceWithin`. -/
private theorem directed_disjointOccurrenceWithin {J : Type*} (A : J → Set (∀ i, E i)) :
    Directed (· ⊆ ·) (fun F : Finset ι => disjointOccurrenceWithin F A) := by
  classical
  intro F G
  exact ⟨F ∪ G, disjointOccurrenceWithin_mono Finset.subset_union_left A,
    disjointOccurrenceWithin_mono Finset.subset_union_right A⟩

end Within

section Transfer

variable {ι : Type*} {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
  (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- A witness set `K ⊆ F` for `A` at `ω` gives a witness set for `sureOn μ F A` at the restriction
of `ω` to `F`: the same coordinates, seen as a finite subset `K'` of `↥F`.
Fixing the coordinates of `K` forces `A` whatever the other coordinates are, so every `x` that
agrees with `ω` on `K'` has `{ω' | mergeOn F x ω' ∈ A}` equal to the whole space, of measure one. -/
private theorem exists_restrict_witness {F K : Finset ι} {A : Set (∀ i, E i)} (hKF : K ⊆ F)
    {ω : ∀ i, E i} (hK : IsWitnessSet A (K : Set ι) ω) :
    ∃ K' : Finset F, (∀ i : F, i ∈ K' ↔ (i : ι) ∈ K) ∧
      IsWitnessSet (sureOn μ F A) (K' : Set F) (F.restrict ω) := by
  classical
  refine ⟨K.subtype (· ∈ F), fun i => by simp [Finset.mem_subtype], ?_⟩
  show agreementCylinder _ (F.restrict ω) ⊆ sureOn μ F A
  intro x hx
  show Measure.infinitePi μ {ω' | mergeOn F x ω' ∈ A} = 1
  have hall : {ω' | mergeOn F x ω' ∈ A} = Set.univ := by
    ext ω'
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    have hK' : agreementCylinder (K : Set ι) ω ⊆ A := hK
    refine hK' ?_
    intro i hi
    have hiF : i ∈ F := hKF (Finset.mem_coe.1 hi)
    rw [mergeOn_of_mem hiF]
    exact hx ⟨i, hiF⟩ (by simpa [Finset.mem_subtype] using hi)
  rw [hall, measure_univ]

/-- Both witnesses inside `F`: the event is inside the preimage, under the restriction to `F`, of
the box occurrence of the two `sureOn` events. -/
private theorem boxOccurrenceWithin_subset (F : Finset ι) (A B : Set (∀ i, E i)) :
    boxOccurrenceWithin F A B ⊆
      F.restrict ⁻¹' boxOccurrence (sureOn μ F A) (sureOn μ F B) := by
  rintro ω ⟨K, L, hKF, hLF, hKL, hK, hL⟩
  obtain ⟨K', hK'm, hK'w⟩ := exists_restrict_witness μ hKF hK
  obtain ⟨L', hL'm, hL'w⟩ := exists_restrict_witness μ hLF hL
  exact ⟨K', L', Finset.disjoint_left.2 fun i h1 h2 =>
    Finset.disjoint_left.1 hKL ((hK'm i).1 h1) ((hL'm i).1 h2), hK'w, hL'w⟩

/-- Family version of `boxOccurrenceWithin_subset`. -/
private theorem disjointOccurrenceWithin_subset {J : Type*} (F : Finset ι)
    (A : J → Set (∀ i, E i)) :
    disjointOccurrenceWithin F A ⊆
      F.restrict ⁻¹' disjointOccurrence (fun j => sureOn μ F (A j)) := by
  rintro ω ⟨K, hKF, hKL, hW⟩
  choose K' hK'm hK'w using fun j => exists_restrict_witness μ (hKF j) (hW j)
  exact ⟨K', fun j l hjl => Finset.disjoint_left.2 fun i h1 h2 =>
    Finset.disjoint_left.1 (hKL hjl) ((hK'm j i).1 h1) ((hK'm l i).1 h2), hK'w⟩

end Transfer

section Countable

variable {ι : Type*} {E : ι → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
  (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- **BK inequality, countably many coordinates** (the statement of `bk_inequality_infinitePi`).
This general countable-coordinate result is proved here as an extension. In the proof of (3.11),
van den Berg and Kesten use a finite-region limit before reducing to finite W and applying
Theorem 3.3. The left side is the outer measure when `A □ B` is not measurable. For each finite
set `F` of coordinates, the event with both witnesses inside `F` has probability at most
`P[A] P[B]` (`bk_inequality_pi` on `↥F` for the `sureOn` events); `A □ B` is the directed
union of these events over the countable type `Finset ι`. -/
theorem bk_inequality_infinitePi_impl [Countable ι] {A B : Set (∀ i, E i)}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    Measure.infinitePi μ (boxOccurrence A B) ≤
      Measure.infinitePi μ A * Measure.infinitePi μ B := by
  -- Step a: one finite set `F` of coordinates.
  have hwithin : ∀ F : Finset ι, Measure.infinitePi μ (boxOccurrenceWithin F A B) ≤
      Measure.infinitePi μ A * Measure.infinitePi μ B := by
    intro F
    calc Measure.infinitePi μ (boxOccurrenceWithin F A B)
        ≤ Measure.infinitePi μ
            (F.restrict ⁻¹' boxOccurrence (sureOn μ F A) (sureOn μ F B)) :=
          measure_mono (boxOccurrenceWithin_subset μ F A B)
      _ ≤ ((Measure.infinitePi μ).map F.restrict) (boxOccurrence (sureOn μ F A) (sureOn μ F B)) :=
          Measure.le_map_apply (Finset.measurable_restrict F).aemeasurable _
      _ = Measure.pi (fun i : F => μ i) (boxOccurrence (sureOn μ F A) (sureOn μ F B)) := by
          rw [Measure.infinitePi_map_restrict]
      _ ≤ Measure.pi (fun i : F => μ i) (sureOn μ F A) *
            Measure.pi (fun i : F => μ i) (sureOn μ F B) :=
          bk_inequality_pi (fun i : F => μ i) (measurableSet_sureOn μ F hAm)
            (measurableSet_sureOn μ F hBm) (isUpperSet_sureOn μ F hA) (isUpperSet_sureOn μ F hB)
      _ ≤ Measure.infinitePi μ A * Measure.infinitePi μ B :=
          mul_le_mul' (pi_sureOn_le_infinitePi μ F hAm) (pi_sureOn_le_infinitePi μ F hBm)
  -- Step b: `A □ B` is the directed union of these events over `Finset ι`.
  calc Measure.infinitePi μ (boxOccurrence A B)
      = Measure.infinitePi μ (⋃ F : Finset ι, boxOccurrenceWithin F A B) := by
        rw [iUnion_boxOccurrenceWithin]
    _ = ⨆ F : Finset ι, Measure.infinitePi μ (boxOccurrenceWithin F A B) :=
        (directed_boxOccurrenceWithin A B).measure_iUnion
    _ ≤ Measure.infinitePi μ A * Measure.infinitePi μ B := iSup_le hwithin

/-- **BK inequality for a finite family, countably many coordinates** (the statement of
`bk_inequality_family_infinitePi`). The proof is that of
`bk_inequality_infinitePi_impl`, with `bk_inequality_family_pi` and a termwise bound of the product
in place of the two-event inequality. -/
theorem bk_inequality_family_infinitePi_impl [Countable ι] {J : Type*} [Fintype J]
    {A : J → Set (∀ i, E i)}
    (hAm : ∀ j, MeasurableSet (A j)) (hA : ∀ j, IsUpperSet (A j)) :
    Measure.infinitePi μ (disjointOccurrence A) ≤ ∏ j, Measure.infinitePi μ (A j) := by
  -- Step a: one finite set `F` of coordinates.
  have hwithin : ∀ F : Finset ι, Measure.infinitePi μ (disjointOccurrenceWithin F A) ≤
      ∏ j, Measure.infinitePi μ (A j) := by
    intro F
    calc Measure.infinitePi μ (disjointOccurrenceWithin F A)
        ≤ Measure.infinitePi μ
            (F.restrict ⁻¹' disjointOccurrence (fun j => sureOn μ F (A j))) :=
          measure_mono (disjointOccurrenceWithin_subset μ F A)
      _ ≤ ((Measure.infinitePi μ).map F.restrict)
            (disjointOccurrence (fun j => sureOn μ F (A j))) :=
          Measure.le_map_apply (Finset.measurable_restrict F).aemeasurable _
      _ = Measure.pi (fun i : F => μ i) (disjointOccurrence (fun j => sureOn μ F (A j))) := by
          rw [Measure.infinitePi_map_restrict]
      _ ≤ ∏ j, Measure.pi (fun i : F => μ i) (sureOn μ F (A j)) :=
          bk_inequality_family_pi (fun i : F => μ i)
            (fun j => measurableSet_sureOn μ F (hAm j)) (fun j => isUpperSet_sureOn μ F (hA j))
      _ ≤ ∏ j, Measure.infinitePi μ (A j) :=
          Finset.prod_le_prod fun j _ => pi_sureOn_le_infinitePi μ F (hAm j)
  -- Step b: `disjointOccurrence A` is the directed union of these events over `Finset ι`.
  calc Measure.infinitePi μ (disjointOccurrence A)
      = Measure.infinitePi μ (⋃ F : Finset ι, disjointOccurrenceWithin F A) := by
        rw [iUnion_disjointOccurrenceWithin]
    _ = ⨆ F : Finset ι, Measure.infinitePi μ (disjointOccurrenceWithin F A) :=
        (directed_disjointOccurrenceWithin A).measure_iUnion
    _ ≤ ∏ j, Measure.infinitePi μ (A j) := iSup_le hwithin

end Countable

end ProbabilityBasics.BK
