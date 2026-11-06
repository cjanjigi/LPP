/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Foundations.BK.Theorem33
public import ProbabilityBasics.Foundations.BK.Witness
public import ProbabilityBasics.Foundations.BK.LeadingOnes
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProductMeasure

/-!
# The BK inequality for bits on a finite index set and for finite chains

This goes beyond van den Berg and Kesten (1985), whose Theorem 3.3 treats bits indexed by `Fin n`
only, and whose box events are their `A ∘ B`.

## Main results

* `bk_bits`: the BK inequality in box form for independent bits indexed by any finite type,
  each bit with its own probability.
* `bk_fin_chains`: the BK inequality in box form for a finite product of finite chains
  `Fin (k i + 1)` with arbitrary probability laws.

## Proof outline

For `bk_bits`, reindex the bits by `Fintype.equivFin`. The reindexing map sends a configuration
to one whose `a`-th bit depends only on the bit `e a`, so it pulls back box occurrences to box
occurrences (`preimage_boxOccurrence_subset`). Then `boxOccurrence_subset_vdBK` and
`theorem_3_3` apply.

For `bk_fin_chains`, index the bits by the sigma type `Σ i, Fin (k i)` and map each block of
bits to its number of leading ones. The image of the bit law is the product of the laws. The
blockwise map is increasing and the `i`-th output depends only on the `i`-th block, so
`preimage_boxOccurrence_subset` reduces the claim to `bk_bits`.

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985), Theorem 3.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityBasics.BK

/-- **The BK inequality for independent bits on a finite index type** (box form). If `A`
and `B` are increasing events of `α → Bool`, `α` finite, and the bits are independent with
`P[bit a = true] = p a`, then `P[A □ B] ≤ P[A] P[B]`. Theorem 3.3 of van den Berg and Kesten
(1985) is the case `α = Fin n`. -/
theorem bk_bits {α : Type*} [Fintype α] (p : α → unitInterval) {A B : Set (α → Bool)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    Measure.pi (fun a => bernoulliMeasure true false (p a)) (boxOccurrence A B) ≤
      Measure.pi (fun a => bernoulliMeasure true false (p a)) A *
        Measure.pi (fun a => bernoulliMeasure true false (p a)) B := by
  classical
  -- the reindexing `e : α ≃ Fin n` and the map `G y a = y (e a)`
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let G := MeasurableEquiv.piCongrLeft (fun _ : α => Bool) e.symm
  have hG : ∀ (y : Fin (Fintype.card α) → Bool) a, G y a = y (e a) := by
    intro y a
    obtain ⟨b, rfl⟩ := e.symm.surjective a
    simp [G, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  -- step 1: `G` carries the bits on `Fin n` to the bits on `α`
  have hpre : ∀ S : Set (α → Bool),
      bernoulliProduct (fun i => p (e.symm i)) (G ⁻¹' S) =
        Measure.pi (fun a => bernoulliMeasure true false (p a)) S := fun S =>
    (measurePreserving_piCongrLeft (fun a => bernoulliMeasure true false (p a)) e.symm
      ).measure_preimage_equiv S
  -- step 2: `G` is increasing, so preimages of increasing events are increasing
  have hmono : Monotone G := fun y y' h a => by
    rw [hG, hG]
    exact h _
  -- step 3: the `a`-th output of `G` depends only on the block `{e a}`
  have hblk : Pairwise fun a b => Disjoint ({e a} : Finset (Fin (Fintype.card α)))
      {e b} := fun a b hab => by
    simpa using e.injective.ne hab
  have hdep : ∀ a (c c' : Fin (Fintype.card α) → Bool),
      (∀ i ∈ ({e a} : Finset (Fin (Fintype.card α))), c i = c' i) → G c a = G c' a :=
    fun a c c' h => by
      rw [hG, hG]
      exact h _ (Finset.mem_singleton_self _)
  -- step 4: Theorem 3.3 on `Fin n` for the pulled-back events
  calc Measure.pi (fun a => bernoulliMeasure true false (p a)) (boxOccurrence A B)
      = bernoulliProduct (fun i => p (e.symm i)) (G ⁻¹' boxOccurrence A B) := (hpre _).symm
    _ ≤ bernoulliProduct (fun i => p (e.symm i))
          (boxOccurrence (G ⁻¹' A) (G ⁻¹' B)) :=
        measure_mono (preimage_boxOccurrence_subset (⇑G) (fun a => {e a}) hblk hdep A B)
    _ ≤ bernoulliProduct (fun i => p (e.symm i))
          (vdBKDisjointOccurrence (G ⁻¹' A) (G ⁻¹' B)) :=
        measure_mono (boxOccurrence_subset_vdBK _ _)
    _ ≤ bernoulliProduct (fun i => p (e.symm i)) (G ⁻¹' A) *
          bernoulliProduct (fun i => p (e.symm i)) (G ⁻¹' B) :=
        theorem_3_3 _ (hA.preimage hmono) (hB.preimage hmono)
    _ = Measure.pi (fun a => bernoulliMeasure true false (p a)) A *
          Measure.pi (fun a => bernoulliMeasure true false (p a)) B := by
        rw [hpre, hpre]

/-- **The BK inequality for finite products of finite chains** (box form).
For increasing events `A` and `B` of `∀ i, Fin (k i + 1)` (`ι'` finite) and arbitrary
probability laws `ν i` on the chains, `P[A □ B] ≤ P[A] P[B]` for the product law. Each chain
law is the image of independent bits under the number of leading ones
(`exists_bernoulli_leadingOnes`), and `bk_bits` is applied to the bits indexed by
`Σ i, Fin (k i)`. -/
theorem bk_fin_chains {ι' : Type*} [Fintype ι'] {k : ι' → ℕ}
    (ν : ∀ i, Measure (Fin (k i + 1))) [∀ i, IsProbabilityMeasure (ν i)]
    {A B : Set (∀ i, Fin (k i + 1))} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    Measure.pi ν (boxOccurrence A B) ≤ Measure.pi ν A * Measure.pi ν B := by
  classical
  -- step 1: bits with the right leading-ones laws, indexed by `Σ i, Fin (k i)`
  choose q hq using fun i => exists_bernoulli_leadingOnes (ν i)
  have : ∀ i, IsProbabilityMeasure (bernoulliProduct (q i)) := fun i => by
    unfold bernoulliProduct
    infer_instance
  let p : (Σ i, Fin (k i)) → unitInterval := fun s => q s.1 s.2
  let μ := Measure.pi (fun s => bernoulliMeasure true false (p s))
  -- the blockwise leading-ones map
  let F : ((Σ i, Fin (k i)) → Bool) → ∀ i, Fin (k i + 1) :=
    fun x i => leadingOnes (fun t => x ⟨i, t⟩)
  -- step 2: the law of `F` is the product of the laws `ν i`
  have hcurry : μ.map (MeasurableEquiv.piCurry fun i (_ : Fin (k i)) => Bool) =
      Measure.pi fun i => bernoulliProduct (q i) := by
    have h := Measure.infinitePi_map_piCurry (X := fun i (_ : Fin (k i)) => Bool)
      (fun i j => bernoulliMeasure true false (q i j))
    simp only [Measure.infinitePi_eq_pi] at h
    exact h
  have hlead : (Measure.pi fun i => bernoulliProduct (q i)).map
      (fun (c : ∀ i, Fin (k i) → Bool) i => leadingOnes (c i)) = Measure.pi ν := by
    rw [Measure.pi_map_pi (fun i => (Measurable.of_discrete (f := leadingOnes)).aemeasurable)]
    simp only [hq]
  have hlaw : μ.map F = Measure.pi ν := by
    rw [← hlead, ← hcurry, Measure.map_map Measurable.of_discrete
      (MeasurableEquiv.measurable _)]
    rfl
  have hpre : ∀ S : Set (∀ i, Fin (k i + 1)), μ (F ⁻¹' S) = Measure.pi ν S := fun S => by
    rw [← hlaw, Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  -- step 3: `F` is increasing, and output `i` depends only on the block of bits `i`
  have hmono : Monotone F := fun x y h i => monotone_leadingOnes fun t => h ⟨i, t⟩
  have hblk : Pairwise fun i j => Disjoint
      (Finset.univ.image (Sigma.mk (β := fun i => Fin (k i)) i))
      (Finset.univ.image (Sigma.mk (β := fun i => Fin (k i)) j)) := fun i j hij => by
    beta_reduce
    rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index]
    rintro _ t rfl ⟨s, hs⟩
    exact hij (Sigma.mk.inj_iff.mp hs).1.symm
  have hdep : ∀ i (c c' : (Σ i, Fin (k i)) → Bool),
      (∀ s ∈ Finset.univ.image (Sigma.mk (β := fun i => Fin (k i)) i), c s = c' s) →
        F c i = F c' i := fun i c c' h => by
    simp only [F]
    congr 1
    funext t
    exact h ⟨i, t⟩ (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)
  -- step 4: `bk_bits` for the pulled-back events
  calc Measure.pi ν (boxOccurrence A B) = μ (F ⁻¹' boxOccurrence A B) := (hpre _).symm
    _ ≤ μ (boxOccurrence (F ⁻¹' A) (F ⁻¹' B)) :=
        measure_mono (preimage_boxOccurrence_subset F
          (fun i => Finset.univ.image (Sigma.mk i)) hblk hdep A B)
    _ ≤ μ (F ⁻¹' A) * μ (F ⁻¹' B) := bk_bits p (hA.preimage hmono) (hB.preimage hmono)
    _ = Measure.pi ν A * Measure.pi ν B := by rw [hpre, hpre]

end ProbabilityBasics.BK
