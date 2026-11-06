/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Foundations.BK.Identification
public import ProbabilityBasics.Foundations.BK.Lemma13
public import ProbabilityBasics.Foundations.BK.NBU
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Order.UpperLower.Prod

/-!
# Theorem 1.6 of van den Berg and Kesten (1985) for `R = ℕ`

* `theorem_1_6_i` is Theorem 1.6 (i), (1.7): for new better than used (NBU) probability
  measures `μ j` on `ℕ` such that `μ j = μ (rep j)`, and an increasing set `A`, the product
  measure of `identImage rep A` is at most that of `A`. The partition with chosen
  representatives is encoded by the map `rep` (`IsRepresentativeMap`). The proof follows the
  paper: apply Lemma 1.3 successively to the pairs `(rep j, j)` with `rep j ≠ j`, by strong
  induction on the number of such `j`.
* `measure_sumUpper_le` is Theorem 1.6 (ii) for an arbitrary increasing set `D` of pairs
  (the paper takes `D = ⋃ (A_l × B_l)`), proved by applying (i) on the index set `α ⊕ α` to
  the partition into the classes `{inl k, inr k}`.
* `theorem_1_6_ii` is (1.8) of the paper.
* `theorem_1_6_iii` is (1.9) of the paper, the case `k = 1` of (ii).

Every subset of `ℕ^ι` is measurable for a finite index type, so, as in `Lemma13`, there is no
measurability hypothesis (the paper appeals to Dellacherie and Meyer for this).

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985), Lemma 1.3 and Theorem 1.6.
-/

@[expose] public section

open MeasureTheory Set
open scoped Pointwise

namespace ProbabilityBasics.BK

section PartI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of indices that are not representatives of themselves. In the proof of
Theorem 1.6 (i) (p. 558) this is the number of applications of Lemma 1.3 still to be made. -/
private abbrev nonFixedCount (rep : ι → ι) : ℕ :=
  (Finset.univ.filter fun k => rep k ≠ k).card

/-- Making `j` a singleton class removes it from the set of non-representatives, and no
other index joins that set. -/
private theorem nonFixedCount_update_lt {rep : ι → ι} {j : ι} (hj : rep j ≠ j) :
    nonFixedCount (Function.update rep j j) < nonFixedCount rep := by
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).2 ⟨j, ?_, ?_⟩)
  · intro k hk
    by_cases hkj : k = j
    · subst hkj
      simp at hk
    · simpa [Function.update_of_ne hkj] using hk
  · simpa using hj
  · simp

omit [Fintype ι] in
/-- Making `j` a singleton class keeps `rep` a representative map (the fixed points are the
old ones together with `j`). -/
private theorem isRepresentativeMap_update {rep : ι → ι} (hrep : IsRepresentativeMap rep)
    {j : ι} (hj : rep j ≠ j) : IsRepresentativeMap (Function.update rep j j) := by
  intro k
  by_cases hkj : k = j
  · subst hkj
    simp
  · have hrk : rep k ≠ j := by
      intro h
      apply hj
      rw [← h, hrep k, h]
    simp [Function.update_of_ne hkj, Function.update_of_ne hrk, hrep k]

/-- One step of the successive application of Lemma 1.3 (p. 558): detaching `j` from its class
does not decrease the measure of the identification image. This is the step
`μ (identImage rep A) ≤ μ (identImage (update rep j j) A)`, which uses
`identImage_eq_pairImage` and Lemma 1.3 for the pair `(rep j, j)`, equal laws
`μ (rep j) = μ j`, and the increasing set `identImage (update rep j j) A`. -/
private theorem measure_identImage_le_update (μ : ι → Measure ℕ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, IsNBU (μ i)) {rep : ι → ι}
    (hrep : IsRepresentativeMap rep) (hμrep : ∀ j, μ j = μ (rep j)) {j : ι} (hj : rep j ≠ j)
    (A : Set (ι → ℕ)) :
    Measure.pi μ (identImage rep A) ≤
      Measure.pi μ (identImage (Function.update rep j j) A) := by
  rw [identImage_eq_pairImage hrep hj A]
  exact lemma_1_3 μ hμ hj (hμrep j).symm (isUpperSet_identImage _ A)

/-- **Theorem 1.6 (i)**, strong induction on the number of non-representatives. -/
private theorem theorem_1_6_i_aux (μ : ι → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, IsNBU (μ i)) (N : ℕ) :
    ∀ {rep : ι → ι}, IsRepresentativeMap rep → (∀ j, μ j = μ (rep j)) →
      nonFixedCount rep = N → ∀ {A : Set (ι → ℕ)}, IsUpperSet A →
        Measure.pi μ (identImage rep A) ≤ Measure.pi μ A := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro rep hrep hμrep hN A hA
    by_cases hall : ∃ j, rep j ≠ j
    · -- Inductive step: detach one non-representative `j` (p. 558, "successively").
      obtain ⟨j, hj⟩ := hall
      have hlt : nonFixedCount (Function.update rep j j) < N :=
        hN ▸ nonFixedCount_update_lt hj
      have hrep' := isRepresentativeMap_update hrep hj
      have hμrep' : ∀ k, μ k = μ (Function.update rep j j k) := by
        intro k
        by_cases hkj : k = j
        · subst hkj
          simp
        · simpa [Function.update_of_ne hkj] using hμrep k
      calc Measure.pi μ (identImage rep A)
          ≤ Measure.pi μ (identImage (Function.update rep j j) A) :=
            measure_identImage_le_update μ hμ hrep hμrep hj A
        _ ≤ Measure.pi μ A := ih _ hlt hrep' hμrep' rfl hA
    · -- Base: every index represents itself, so `rep = id` and the image is `A`.
      have hid : rep = id := funext fun k => not_not.1 fun h => hall ⟨k, h⟩
      subst hid
      exact (congrArg (Measure.pi μ) (identImage_id hA)).le

/-- **Theorem 1.6 (i)** of van den Berg and Kesten (1985), p. 558, for `R = ℕ`: let `μ j` be NBU
probability measures on `ℕ`, let the partition with representatives be encoded by `rep`, with
`μ j = μ (rep j)` (measures in one class are equal), and let `A` be increasing. Then the product
measure of the image of `A` under identification is at most that of `A`, (1.7).

The paper says: apply Lemma 1.3 successively to all pairs `(i, j)` with `i = i_F` and
`j ∈ F`, `j ≠ i`. The induction over these pairs is by the number of `j` with `rep j ≠ j`; the
identity `identImage_eq_pairImage` that makes each step a pair image is the omitted
bookkeeping. -/
theorem theorem_1_6_i (μ : ι → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, IsNBU (μ i)) {rep : ι → ι} (hrep : IsRepresentativeMap rep)
    (hμrep : ∀ j, μ j = μ (rep j)) {A : Set (ι → ℕ)} (hA : IsUpperSet A) :
    Measure.pi μ (identImage rep A) ≤ Measure.pi μ A :=
  theorem_1_6_i_aux μ hμ _ hrep hμrep rfl hA

end PartI

section PartII

variable {α : Type*}

/-- The map from points of `ℕ^(α ⊕ α)` to pairs of points of `ℕ^α`: the first `m` and the last
`m` coordinates (the underlying map of `MeasurableEquiv.sumPiEquivProdPi`). -/
private abbrev splitPair (z : α ⊕ α → ℕ) : (α → ℕ) × (α → ℕ) := (z ∘ Sum.inl, z ∘ Sum.inr)

/-- The index set `α ⊕ α` carries the measure `ν` on both halves (proof of (ii), p. 558:
`μ_i = ν_i` and `μ_{m+i} = ν_i`). -/
private instance instIsProbabilityMeasureSumElim (ν : α → Measure ℕ)
    [∀ k, IsProbabilityMeasure (ν k)] (i : α ⊕ α) :
    IsProbabilityMeasure (Sum.elim ν ν i) := by
  cases i with
  | inl k => exact (inferInstance : IsProbabilityMeasure (ν k))
  | inr k => exact (inferInstance : IsProbabilityMeasure (ν k))

/-- The doubled measure `Sum.elim ν ν` is NBU in every coordinate when `ν` is. -/
private theorem isNBU_sumElim (ν : α → Measure ℕ) (hν : ∀ k, IsNBU (ν k)) (i : α ⊕ α) :
    IsNBU (Sum.elim ν ν i) := by
  cases i with
  | inl k => exact hν k
  | inr k => exact hν k

variable [Fintype α]

/-- The doubled product measure on `ℕ^(α ⊕ α)` is carried to `ν ⊗ ν` on pairs, by `splitPair`
(proof of (ii), p. 558: `μ = ν × ν`). -/
private theorem measure_preimage_splitPair (ν : α → Measure ℕ)
    [∀ k, IsProbabilityMeasure (ν k)] (D : Set ((α → ℕ) × (α → ℕ))) :
    Measure.pi (Sum.elim ν ν) (splitPair ⁻¹' D) =
      ((Measure.pi ν).prod (Measure.pi ν)) D :=
  (measurePreserving_sumPiEquivProdPi (X := fun _ : α ⊕ α => ℕ) (Sum.elim ν ν)
    ).measure_preimage_equiv D

/-- **Theorem 1.6 (ii) for any increasing set** (p. 558-559). Let `ν k` be NBU probability
measures on `ℕ` and `D` an increasing set of pairs of points of `ℕ^α`. Then the `ν`-measure of
the set `sumUpper D` of points above some `a + b`, `(a, b) ∈ D`, is at most the `ν ⊗ ν`-measure
of `D`. The paper takes `D = ⋃ (A_l × B_l)`.

Proof, as in the paper: put `μ = ν × ν` on `α ⊕ α`, with the classes `{inl k, inr k}` and
representatives `inl k`, apply (1.7) to the set `D` seen in `ℕ^(α ⊕ α)`, and note that the
image `A*` is `sumUpper D` times `ℕ^α`, which has the same measure as `sumUpper D`. -/
theorem measure_sumUpper_le (ν : α → Measure ℕ) [∀ k, IsProbabilityMeasure (ν k)]
    (hν : ∀ k, IsNBU (ν k)) {D : Set ((α → ℕ) × (α → ℕ))} (hD : IsUpperSet D) :
    Measure.pi ν (sumUpper D) ≤ ((Measure.pi ν).prod (Measure.pi ν)) D := by
  classical
  -- `D` seen as an increasing subset of `ℕ^(α ⊕ α)`.
  have hD' : IsUpperSet (splitPair ⁻¹' D) :=
    hD.preimage fun z w hzw => ⟨fun k => hzw (Sum.inl k), fun k => hzw (Sum.inr k)⟩
  -- The image under identification of the classes `{inl k, inr k}` (the set `A*` of p. 559).
  have image_eq : identImage (Sum.elim Sum.inl Sum.inl : α ⊕ α → α ⊕ α) (splitPair ⁻¹' D) =
      splitPair ⁻¹' (sumUpper D ×ˢ (univ : Set (α → ℕ))) := by
    rw [identImage_sum_elim]
    ext x
    exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  have class_laws : ∀ j, Sum.elim ν ν j =
      Sum.elim ν ν ((Sum.elim Sum.inl Sum.inl : α ⊕ α → α ⊕ α) j) := by
    intro j
    cases j <;> rfl
  -- (1.7) on the index set `α ⊕ α`.
  have key := theorem_1_6_i (Sum.elim ν ν) (isNBU_sumElim ν hν)
    isRepresentativeMap_sumElim class_laws hD'
  rw [image_eq, measure_preimage_splitPair, measure_preimage_splitPair, Measure.prod_prod,
    measure_univ, mul_one] at key
  exact key

end PartII

section PartIIIAndIV

variable {α : Type*} [Fintype α]

/-- **Theorem 1.6 (ii)** of van den Berg and Kesten (1985), (1.8), p. 558, for `R = ℕ`: for NBU
probability measures `ν k` on `ℕ` and increasing sets `A l`, `B l` of `ℕ^α`, `l = 1, ..., q`,
`ν (⋃ (A l + B l)) ≤ (ν × ν) (⋃ (A l × B l))`. The union of the products is increasing, so
this is `measure_sumUpper_le` for `D = ⋃ (A l × B l)`, with `sumUpper D = ⋃ (A l + B l)`. -/
theorem theorem_1_6_ii (ν : α → Measure ℕ) [∀ k, IsProbabilityMeasure (ν k)]
    (hν : ∀ k, IsNBU (ν k)) {q : ℕ} {A B : Fin q → Set (α → ℕ)}
    (hA : ∀ l, IsUpperSet (A l)) (hB : ∀ l, IsUpperSet (B l)) :
    Measure.pi ν (⋃ l, A l + B l) ≤
      ((Measure.pi ν).prod (Measure.pi ν)) (⋃ l, A l ×ˢ B l) := by
  have hD : IsUpperSet (⋃ l, A l ×ˢ B l) := isUpperSet_iUnion fun l => (hA l).prod (hB l)
  have key := measure_sumUpper_le ν hν hD
  rwa [sumUpper_iUnion_prod hB] at key

/-- **Theorem 1.6 (iii)** of van den Berg and Kesten (1985), (1.9), p. 559, for `R = ℕ`: the
product `ν` of NBU probability measures on `ℕ` is strongly new better than used,
`ν (A + B) ≤ ν A * ν B` for increasing sets `A` and `B`. This is (ii) with `q = 1`. -/
theorem theorem_1_6_iii (ν : α → Measure ℕ) [∀ k, IsProbabilityMeasure (ν k)]
    (hν : ∀ k, IsNBU (ν k)) {A B : Set (α → ℕ)} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    Measure.pi ν (A + B) ≤ Measure.pi ν A * Measure.pi ν B := by
  have key := theorem_1_6_ii ν hν (q := 1) (A := fun _ => A) (B := fun _ => B)
    (fun _ => hA) (fun _ => hB)
  simpa [Set.iUnion_const, Measure.prod_prod] using key

end PartIIIAndIV

end ProbabilityBasics.BK
