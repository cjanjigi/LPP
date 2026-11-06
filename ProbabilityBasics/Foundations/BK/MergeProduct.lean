/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Order.UpperLower.Basic

/-!
# Merging a finite block of coordinates into an infinite product

This file provides the finite-block merge used by the countable-coordinate extension proved in
`Countable.lean`. In the proof of (3.11), van den Berg and Kesten use a finite-region limit before
reducing to finite W and applying Theorem 3.3.

For a finite set `F` of coordinates, a point `x` of the product over `F` and a point `ω` of the
full product, `mergeOn F x ω` takes the coordinates of `x` on `F` and those of `ω` elsewhere.
This file contains

* `mergeOn`, this operation, with its basic facts (`mergeOn_of_mem`, `mergeOn_of_notMem`,
  `restrict_mergeOn`, `mergeOn_restrict`, `mergeOn_mono_left`, `measurable_mergeOn`);
* `map_mergeOn_infinitePi`: if `x` follows the finite product law on `F` and `ω` follows the
  infinite product law, independently, then `mergeOn F x ω` follows the infinite product law;
* `sureOn`, the values on `F` for which an event holds almost surely whatever the other
  coordinates are, with `measurableSet_sureOn`, `isUpperSet_sureOn` and
  `pi_sureOn_le_infinitePi`.

Each statement carries only the binders it uses (measurable spaces, probability measures, and
a preorder for the monotonicity lemma), so a consumer with the full class of the statement
`bk_inequality_infinitePi` can supply them all.

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityBasics.BK

variable {ι : Type*} {E : ι → Type*}

/-! ### The merge operation -/

open scoped Classical in
/-- `mergeOn F x ω` is the point of the full product that agrees with `x` on the finite set `F`
and with `ω` outside `F`. -/
noncomputable def mergeOn (F : Finset ι) (x : ∀ i : F, E i) (ω : ∀ i, E i) : ∀ i, E i :=
  fun i => if h : i ∈ F then x ⟨i, h⟩ else ω i

/-- On `F`, `mergeOn F x ω` reads `x`. -/
theorem mergeOn_of_mem {F : Finset ι} {x : ∀ i : F, E i} {ω : ∀ i, E i} {i : ι} (h : i ∈ F) :
    mergeOn F x ω i = x ⟨i, h⟩ := by
  simp [mergeOn, h]

/-- Outside `F`, `mergeOn F x ω` reads `ω`. -/
theorem mergeOn_of_notMem {F : Finset ι} {x : ∀ i : F, E i} {ω : ∀ i, E i} {i : ι} (h : i ∉ F) :
    mergeOn F x ω i = ω i := by
  simp [mergeOn, h]

/-- Restricting `mergeOn F x ω` to `F` gives back `x`. -/
theorem restrict_mergeOn (F : Finset ι) (x : ∀ i : F, E i) (ω : ∀ i, E i) :
    F.restrict (mergeOn F x ω) = x :=
  funext fun i => mergeOn_of_mem i.2

/-- Merging the restriction of `ω` to `F` into `ω` changes nothing. -/
theorem mergeOn_restrict (F : Finset ι) (ω : ∀ i, E i) : mergeOn F (F.restrict ω) ω = ω := by
  funext i
  by_cases h : i ∈ F
  · exact mergeOn_of_mem h
  · exact mergeOn_of_notMem h

/-- `mergeOn` is increasing in the block `x` when each coordinate type is a preorder. -/
theorem mergeOn_mono_left [∀ i, Preorder (E i)] {F : Finset ι} {x y : ∀ i : F, E i}
    (hxy : x ≤ y) (ω : ∀ i, E i) : mergeOn F x ω ≤ mergeOn F y ω := by
  intro i
  by_cases h : i ∈ F
  · rw [mergeOn_of_mem h, mergeOn_of_mem h]
    exact hxy ⟨i, h⟩
  · rw [mergeOn_of_notMem h, mergeOn_of_notMem h]

section Measure

variable [∀ i, MeasurableSpace (E i)]

/-- The merge operation `(x, ω) ↦ mergeOn F x ω` is measurable for the product sigma-algebra. -/
theorem measurable_mergeOn (F : Finset ι) :
    Measurable (fun p : (∀ i : F, E i) × (∀ i, E i) => mergeOn F p.1 p.2) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i ∈ F
  · simp only [mergeOn_of_mem h]
    exact (measurable_pi_apply (⟨i, h⟩ : F)).comp measurable_fst
  · simp only [mergeOn_of_notMem h]
    exact (measurable_pi_apply i).comp measurable_snd

variable (μ : ∀ i, Measure (E i))

/-- `sureOn μ F A` is the set of values `x` on the finite set `F` for which the event `A` holds
almost surely when the other coordinates follow the infinite product law: the set of `x` with
`infinitePi μ {ω | mergeOn F x ω ∈ A} = 1`. -/
def sureOn (F : Finset ι) (A : Set (∀ i, E i)) : Set (∀ i : F, E i) :=
  {x | Measure.infinitePi μ {ω | mergeOn F x ω ∈ A} = 1}

variable [∀ i, IsProbabilityMeasure (μ i)]

/-- **Merging a finite block into an infinite product.** Draw `x` from the finite product law on
`F` and `ω` from the infinite product law, independently. Then `mergeOn F x ω` follows the
infinite product law. Proof: both sides give the same mass to finite boxes
(`Measure.eq_infinitePi`). -/
theorem map_mergeOn_infinitePi (F : Finset ι) :
    ((Measure.pi fun i : F => μ i).prod (Measure.infinitePi μ)).map
      (fun p : (∀ i : F, E i) × (∀ i, E i) => mergeOn F p.1 p.2) = Measure.infinitePi μ := by
  classical
  refine Measure.eq_infinitePi μ fun s t ht => ?_
  -- Step a: the box `Set.pi s t` is measurable, so the image measure is the measure of its
  -- preimage.
  have hbox : MeasurableSet ((s : Set ι).pi t) :=
    MeasurableSet.pi s.countable_toSet fun i _ => ht i
  rw [Measure.map_apply (measurable_mergeOn F) hbox]
  -- Step b: the preimage is a rectangle. Its first side constrains the coordinates in `F ∩ s`,
  -- its second side the coordinates in `s \ F`.
  have hpre : (fun p : (∀ i : F, E i) × (∀ i, E i) => mergeOn F p.1 p.2) ⁻¹' ((s : Set ι).pi t) =
      (Set.univ.pi fun i : F => if (i : ι) ∈ s then t i else Set.univ) ×ˢ
        ((↑(s \ F) : Set ι).pi t) := by
    ext ⟨x, ω⟩
    constructor
    · intro h
      refine ⟨fun i _ => ?_, fun i hi => ?_⟩
      · by_cases hs : (i : ι) ∈ s
        · have hi : mergeOn F x ω i ∈ t i := h i hs
          rw [mergeOn_of_mem i.2] at hi
          show x i ∈ if (i : ι) ∈ s then t i else Set.univ
          simp only [hs, ↓reduceIte]
          exact hi
        · show x i ∈ if (i : ι) ∈ s then t i else Set.univ
          simp [hs]
      · have hmem := Finset.mem_sdiff.1 hi
        have hi' : mergeOn F x ω i ∈ t i := h i hmem.1
        rw [mergeOn_of_notMem hmem.2] at hi'
        exact hi'
    · rintro ⟨h1, h2⟩ i hi
      by_cases hF : i ∈ F
      · have hi2 : i ∈ s := hi
        have hi' : x ⟨i, hF⟩ ∈ if (i : ι) ∈ s then t i else Set.univ :=
          h1 ⟨i, hF⟩ (mem_univ _)
        simp only [hi2, ↓reduceIte] at hi'
        show mergeOn F x ω i ∈ t i
        rw [mergeOn_of_mem hF]
        exact hi'
      · show mergeOn F x ω i ∈ t i
        rw [mergeOn_of_notMem hF]
        exact h2 i (Finset.mem_sdiff.2 ⟨hi, hF⟩)
  -- Step c: product of the two sides by `Measure.prod_prod`, `Measure.pi_pi`, `infinitePi_pi`.
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.infinitePi_pi μ fun i _ => ht i]
  -- Step d: finite-product bookkeeping.
  have hfirst : (∏ i : F, μ i (if (i : ι) ∈ s then t i else Set.univ)) =
      ∏ i ∈ s ∩ F, μ i (t i) := by
    rw [Finset.prod_coe_sort F (fun i => μ i (if i ∈ s then t i else Set.univ))]
    calc ∏ i ∈ F, μ i (if i ∈ s then t i else Set.univ)
        = ∏ i ∈ F, if i ∈ s then μ i (t i) else 1 :=
          Finset.prod_congr rfl fun i _ => by split_ifs <;> simp
      _ = ∏ i ∈ F with i ∈ s, μ i (t i) := (Finset.prod_filter _ _).symm
      _ = ∏ i ∈ s ∩ F, μ i (t i) := by rw [Finset.filter_mem_eq_inter, Finset.inter_comm]
  rw [hfirst]
  exact Finset.prod_inter_mul_prod_sdiff s F fun i => μ i (t i)

/-- The set `sureOn μ F A` is measurable when `A` is. The map `x ↦ P {ω | mergeOn F x ω ∈ A}` is
measurable by `measurable_measure_prodMk_left`. -/
theorem measurableSet_sureOn (F : Finset ι) {A : Set (∀ i, E i)} (hA : MeasurableSet A) :
    MeasurableSet (sureOn μ F A) := by
  have hS : MeasurableSet
      ((fun p : (∀ i : F, E i) × (∀ i, E i) => mergeOn F p.1 p.2) ⁻¹' A) :=
    measurable_mergeOn F hA
  exact measurable_measure_prodMk_left (ν := Measure.infinitePi μ) hS (measurableSet_singleton 1)

/-- The set `sureOn μ F A` is an upper set when `A` is: raising the block `x` raises the merged
point, and an upper set stays an upper set under a monotone map. -/
theorem isUpperSet_sureOn [∀ i, Preorder (E i)] (F : Finset ι) {A : Set (∀ i, E i)}
    (hA : IsUpperSet A) : IsUpperSet (sureOn μ F A) := by
  intro x y hxy hx
  have hx' : Measure.infinitePi μ {ω | mergeOn F x ω ∈ A} = 1 := hx
  have hsub : {ω | mergeOn F x ω ∈ A} ⊆ {ω | mergeOn F y ω ∈ A} :=
    fun ω hω => hA (mergeOn_mono_left hxy ω) hω
  show Measure.infinitePi μ {ω | mergeOn F y ω ∈ A} = 1
  refine le_antisymm prob_le_one ?_
  calc (1 : ℝ≥0∞) = Measure.infinitePi μ {ω | mergeOn F x ω ∈ A} := hx'.symm
    _ ≤ Measure.infinitePi μ {ω | mergeOn F y ω ∈ A} := measure_mono hsub

/-- The finite product law of `sureOn μ F A` is at most the probability of `A`: the values `x`
with conditional probability one carry mass at most `P A`. Proof: by
`map_mergeOn_infinitePi` and `Measure.prod_apply`, `P A` is the integral over `x` of the
conditional probability of `A`, which is `1` on `sureOn μ F A`. -/
theorem pi_sureOn_le_infinitePi (F : Finset ι) {A : Set (∀ i, E i)} (hA : MeasurableSet A) :
    Measure.pi (fun i : F => μ i) (sureOn μ F A) ≤ Measure.infinitePi μ A := by
  set S : Set ((∀ i : F, E i) × (∀ i, E i)) :=
    (fun p : (∀ i : F, E i) × (∀ i, E i) => mergeOn F p.1 p.2) ⁻¹' A with hSdef
  have hS : MeasurableSet S := measurable_mergeOn F hA
  -- `P A` is the product measure of `S`.
  have hPA : Measure.infinitePi μ A =
      ((Measure.pi fun i : F => μ i).prod (Measure.infinitePi μ)) S :=
    (congrArg (fun ν : Measure (∀ i, E i) => ν A) (map_mergeOn_infinitePi μ F)).symm.trans
      (Measure.map_apply (measurable_mergeOn F) hA)
  rw [hPA, Measure.prod_apply hS]
  calc Measure.pi (fun i : F => μ i) (sureOn μ F A)
      = ∫⁻ x, (sureOn μ F A).indicator 1 x ∂(Measure.pi fun i : F => μ i) :=
        (lintegral_indicator_one (measurableSet_sureOn μ F hA)).symm
    _ ≤ ∫⁻ x, Measure.infinitePi μ (Prod.mk x ⁻¹' S) ∂(Measure.pi fun i : F => μ i) := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ sureOn μ F A
        · have hx' : Measure.infinitePi μ (Prod.mk x ⁻¹' S) = 1 := hx
          rw [indicator_of_mem hx, hx']
          rfl
        · rw [indicator_of_notMem hx]
          exact zero_le

end Measure

end ProbabilityBasics.BK
