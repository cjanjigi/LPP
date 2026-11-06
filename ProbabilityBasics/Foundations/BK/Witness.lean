/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Frozen.Foundations.BK.AgreementCylinder
public import ProbabilityBasics.Frozen.Foundations.BK.IsWitnessSet
public import ProbabilityBasics.Frozen.Foundations.BK.BoxOccurrence
public import ProbabilityBasics.Frozen.Foundations.BK.DisjointOccurrence
public import ProbabilityBasics.Frozen.Foundations.BK.OnesOf
public import ProbabilityBasics.Frozen.Foundations.BK.ConfigOfOnes
public import ProbabilityBasics.Frozen.Foundations.BK.VdBKDisjointOccurrence
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Disjoint

/-!
# Witness sets of increasing events

Witness sets and the box occurrence of increasing events, following van den Berg and Kesten (1985).
Moving a configuration up keeps its witness sets, so the box occurrence and the disjoint occurrence
of increasing events are increasing. Witness sets also pull back along maps that act block by
block. On `{0,1}ⁿ` the box occurrence `A □ B` of increasing events equals the paper's `A ∘ B`.

## Main results

- `isWitnessSet_of_le`: a witness set stays a witness set when the configuration moves up.
- `boxOccurrence_isUpperSet`, `disjointOccurrence_isUpperSet`: occurrences of increasing events are
  increasing.
- `preimage_boxOccurrence_subset`, `preimage_disjointOccurrence_subset`: occurrences pull back along
  maps that act block by block.
- `boxOccurrence_subset_vdBK`, `vdBK_subset_boxOccurrence`: the two inclusions between `A □ B` and
  `A ∘ B` on `{0,1}ⁿ`.

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985), Remark 3.5 (d).
-/

@[expose] public section

namespace ProbabilityBasics.BK

variable {ι : Type*} {E : ι → Type*}

/-! ### Witness sets of increasing events

An event is increasing (an upper set) when moving a configuration up keeps it
inside the event. These are the "positive" events of van den Berg and Kesten (1985). The lemmas
below are beyond the paper. -/

/-- Moving the configuration up keeps a witness set. If the coordinates in `K`
witness the increasing event `A` at `ω`, and `ω ≤ ω'`, then `K` witnesses `A`
at `ω'`. Plain meaning: every configuration that agrees with `ω'` on `K` is
above a configuration that agrees with `ω` on `K`, so it is in `A` too. -/
theorem isWitnessSet_of_le [∀ i, Preorder (E i)] {A : Set (∀ i, E i)}
    (hA : IsUpperSet A) {K : Set ι} {ω ω' : ∀ i, E i} (hle : ω ≤ ω')
    (hK : IsWitnessSet A K ω) : IsWitnessSet A K ω' := by
  classical
  have hK' : agreementCylinder K ω ⊆ A := hK
  show agreementCylinder K ω' ⊆ A
  intro η hη
  -- `ζ` takes the values of `ω` on `K` and the values of `η` off `K`.
  let ζ : ∀ i, E i := fun i => if i ∈ K then ω i else η i
  have hζK : ζ ∈ agreementCylinder K ω := by
    show ∀ i ∈ K, ζ i = ω i
    intro i hi
    simp [ζ, hi]
  have hζη : ζ ≤ η := by
    intro i
    by_cases hi : i ∈ K
    · have hηi : η i = ω' i := hη i hi
      show (if i ∈ K then ω i else η i) ≤ η i
      simp only [hi, ↓reduceIte, hηi]
      exact hle i
    · show (if i ∈ K then ω i else η i) ≤ η i
      simp [hi]
  exact hA hζη (hK' hζK)

/-- A box occurrence of increasing events is increasing. The disjoint occurrence `A □ B` is as in
(3.8) of van den Berg and Kesten (1985); the statement is beyond the paper in this form. -/
theorem boxOccurrence_isUpperSet [∀ i, Preorder (E i)] {A B : Set (∀ i, E i)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) : IsUpperSet (boxOccurrence A B) := by
  intro ω ω' hle hω
  obtain ⟨K, L, hKL, hK, hL⟩ := hω
  exact ⟨K, L, hKL, isWitnessSet_of_le hA hle hK, isWitnessSet_of_le hB hle hL⟩

/-- A disjoint occurrence of a family of increasing events is increasing. -/
theorem disjointOccurrence_isUpperSet {J : Type*} [∀ i, Preorder (E i)]
    {A : J → Set (∀ i, E i)} (hA : ∀ j, IsUpperSet (A j)) :
    IsUpperSet (disjointOccurrence A) := by
  intro ω ω' hle hω
  obtain ⟨K, hK, hW⟩ := hω
  exact ⟨K, hK, fun j => isWitnessSet_of_le (hA j) hle (hW j)⟩

/-! ### Maps that act block by block

Let `F` send a configuration on `ι` to a configuration on `κ`. Suppose the
`a`-th output of `F` depends only on the input coordinates in the finite
block `blk a`, and distinct blocks are disjoint. Then witness sets of the
outputs pull back to witness sets of the inputs, by taking unions of blocks.
This is beyond the paper. -/

/-- The unions of disjoint blocks of coordinates of distinct outputs are
disjoint. -/
private theorem disjoint_biUnion_blocks {κ : Type*} [DecidableEq ι] {blk : κ → Finset ι}
    (hblk : Pairwise fun a b => Disjoint (blk a) (blk b)) {K L : Finset κ}
    (hKL : Disjoint K L) : Disjoint (K.biUnion blk) (L.biUnion blk) := by
  rw [Finset.disjoint_left]
  intro x hxK hxL
  obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hxK
  obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hxL
  have hab : a ≠ b := fun h => Finset.disjoint_left.mp hKL ha (by rw [h]; exact hb)
  exact Finset.disjoint_left.mp (hblk hab) hxa hxb

/-- A witness set of the outputs at `F ω` pulls back to the union of its
blocks, as a witness set of the inputs at `ω`. -/
private theorem isWitnessSet_preimage {κ : Type*} {G : κ → Type*} [DecidableEq ι]
    (F : (∀ i, E i) → ∀ a, G a) (blk : κ → Finset ι)
    (hF : ∀ a c c', (∀ i ∈ blk a, c i = c' i) → F c a = F c' a)
    {A : Set (∀ a, G a)} {K : Finset κ} {ω : ∀ i, E i}
    (hK : IsWitnessSet A (K : Set κ) (F ω)) :
    IsWitnessSet (F ⁻¹' A) ((K.biUnion blk : Finset ι) : Set ι) ω := by
  have hK' : agreementCylinder (K : Set κ) (F ω) ⊆ A := hK
  show agreementCylinder _ ω ⊆ F ⁻¹' A
  intro η hη
  -- `hη : ∀ i ∈ ⋃ a ∈ K, blk a, η i = ω i`. Each output in `K` depends only on
  -- its block, and the blocks are covered by `hη`, so `F η` agrees with `F ω`.
  have hagree : F η ∈ agreementCylinder (K : Set κ) (F ω) := by
    show ∀ a ∈ (K : Set κ), F η a = F ω a
    intro a ha
    refine hF a η ω ?_
    intro i hi
    exact hη i (Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨a, Finset.mem_coe.mp ha, hi⟩))
  exact hK' hagree

/-- Block-wise preimage of a box occurrence. If the outputs of `F` depend only
on their blocks, then `F ⁻¹' (A □ B) ⊆ (F ⁻¹' A) □ (F ⁻¹' B)`. This is beyond
the paper; it covers reindexing (`blk a = {e a}`) and encodings in which
each output is a block of inputs. -/
theorem preimage_boxOccurrence_subset {κ : Type*} {G : κ → Type*}
    (F : (∀ i, E i) → ∀ a, G a) (blk : κ → Finset ι)
    (hblk : Pairwise fun a b => Disjoint (blk a) (blk b))
    (hF : ∀ a c c', (∀ i ∈ blk a, c i = c' i) → F c a = F c' a)
    (A B : Set (∀ a, G a)) :
    F ⁻¹' boxOccurrence A B ⊆ boxOccurrence (F ⁻¹' A) (F ⁻¹' B) := by
  classical
  intro ω hω
  obtain ⟨K, L, hKL, hK, hL⟩ := hω
  exact ⟨K.biUnion blk, L.biUnion blk, disjoint_biUnion_blocks hblk hKL,
    isWitnessSet_preimage F blk hF hK, isWitnessSet_preimage F blk hF hL⟩

/-- Block-wise preimage of a disjoint occurrence of a family. Beyond the
paper; same hypotheses as `preimage_boxOccurrence_subset`. -/
theorem preimage_disjointOccurrence_subset {κ J : Type*} {G : κ → Type*}
    (F : (∀ i, E i) → ∀ a, G a) (blk : κ → Finset ι)
    (hblk : Pairwise fun a b => Disjoint (blk a) (blk b))
    (hF : ∀ a c c', (∀ i ∈ blk a, c i = c' i) → F c a = F c' a)
    (A : J → Set (∀ a, G a)) :
    F ⁻¹' disjointOccurrence A ⊆ disjointOccurrence (fun j => F ⁻¹' A j) := by
  classical
  intro ω hω
  obtain ⟨K, hK, hW⟩ := hω
  exact ⟨fun j => (K j).biUnion blk,
    fun j l hjl => disjoint_biUnion_blocks hblk (hK hjl),
    fun j => isWitnessSet_preimage F blk hF (hW j)⟩

/-! ### Disjoint occurrence on `{0,1}^n` (Remark 3.5 (d) of van den Berg and Kesten (1985))

The paper states that for increasing events `A` and `B`, `A □ B` equals
`A ∘ B` (the "occur disjointly" event of Section 3). The two inclusions below
are the two directions. The paper gives no argument. -/

section Cube

variable {n : ℕ}

/-- A configuration with ones exactly `S` lies below every configuration that
agrees with `ω` on `S`, when `S` is contained in the ones of `ω`. -/
private theorem configOfOnes_le {ω η : Fin n → Bool} {S : Finset (Fin n)}
    (hS : S ⊆ onesOf ω) (hη : ∀ i ∈ S, η i = ω i) : configOfOnes S ≤ η := by
  intro i
  by_cases hi : i ∈ S
  · have hωi : ω i = true := by
      have hmem := hS hi
      simpa [onesOf] using hmem
    simp [configOfOnes, hi, hη i hi, hωi]
  · simp [configOfOnes, hi]

/-- If `S` is inside the ones of `ω` and the configuration with ones `S` is in
an increasing event `A`, then `S` witnesses `A` at `ω`. -/
private theorem isWitnessSet_of_config {A : Set (Fin n → Bool)} (hA : IsUpperSet A)
    {ω : Fin n → Bool} {S : Finset (Fin n)} (hS : S ⊆ onesOf ω)
    (hmem : configOfOnes S ∈ A) : IsWitnessSet A (S : Set (Fin n)) ω := by
  show agreementCylinder _ ω ⊆ A
  intro η hη
  exact hA (configOfOnes_le hS (fun i hi => hη i (Finset.mem_coe.mpr hi))) hmem

/-- Remark 3.5 (d) of van den Berg and Kesten (1985), first half. For any events `A` and `B`
on `{0,1}^n`, a disjoint occurrence `A □ B` (witnessed by two disjoint sets of
coordinates) is contained in the paper's `A ∘ B`. No monotonicity is needed. -/
theorem boxOccurrence_subset_vdBK (A B : Set (Fin n → Bool)) :
    boxOccurrence A B ⊆ vdBKDisjointOccurrence A B := by
  intro ω hω
  obtain ⟨K, L, hKL, hK, hL⟩ := hω
  have hK' : agreementCylinder (K : Set (Fin n)) ω ⊆ A := hK
  have hL' : agreementCylinder (L : Set (Fin n)) ω ⊆ B := hL
  refine ⟨K ∩ onesOf ω, Finset.inter_subset_right, ?_, ?_⟩
  · -- The ones `K ∩ K(ω)` agree with `ω` on `K`.
    refine hK' ?_
    show ∀ i ∈ (K : Set (Fin n)), configOfOnes (K ∩ onesOf ω) i = ω i
    intro i hi
    have hiK : i ∈ K := Finset.mem_coe.mp hi
    cases h : ω i <;> simp [configOfOnes, onesOf, hiK, h]
  · -- The ones `K(ω) \ (K ∩ K(ω))` agree with `ω` on `L`, since `L` misses `K`.
    apply hL'
    show ∀ i ∈ (L : Set (Fin n)), configOfOnes (onesOf ω \ (K ∩ onesOf ω)) i = ω i
    intro i hi
    have hiL : i ∈ L := Finset.mem_coe.mp hi
    have hiK : i ∉ K := fun h => Finset.disjoint_left.mp hKL h hiL
    cases h : ω i <;> simp [configOfOnes, onesOf, hiK, h]

/-- Remark 3.5 (d) of van den Berg and Kesten (1985), second half. For increasing events `A` and
`B` on `{0,1}^n`, the paper's `A ∘ B` is contained in the disjoint occurrence
`A □ B`. Both events must be increasing. -/
theorem vdBK_subset_boxOccurrence {A B : Set (Fin n → Bool)} (hA : IsUpperSet A)
    (hB : IsUpperSet B) : vdBKDisjointOccurrence A B ⊆ boxOccurrence A B := by
  intro ω hω
  obtain ⟨K, hKsub, hKA, hLB⟩ := hω
  refine ⟨K, onesOf ω \ K, Finset.disjoint_left.mpr ?_,
    isWitnessSet_of_config hA hKsub hKA,
    isWitnessSet_of_config hB Finset.sdiff_subset hLB⟩
  intro i hiK hiL
  exact (Finset.mem_sdiff.mp hiL).2 hiK

end Cube

end ProbabilityBasics.BK
