/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Foundations.BK.FiniteChains
public import ProbabilityBasics.Foundations.BK.RoundingLimit

/-!
# The BK inequality for finitely many coordinates in ordered spaces

The BK inequality for a finite product of ordered spaces. This goes beyond van den Berg and Kesten
(1985), whose Theorem 3.3 treats bits only. The proof rounds every coordinate up to finitely many
levels (Step 1) and then removes the rounding one coordinate at a time (Step 2).

## Main results

* `bk_roundedSet_empty` (Step 1): if every coordinate is rounded up to finitely many levels, then
  `P[A □ B] ≤ P[rounded A] P[rounded B]`. The proof maps each coordinate to its rank among the
  levels, which lands in a finite chain, and applies `bk_fin_chains`.
* `bk_inequality_pi` (Step 2): the BK inequality for a finite product of ordered spaces in the
  class of `bk_inequality`, with the same statement. The rounding is removed one
  coordinate at a time, using `tendsto_measure_roundCoord`.

## Proof outline

Step 1. Write `Λ' i = Λ i (N i)` and let `r` send a point to the ranks of its coordinates among the
levels. The chain set `{v | boxAbove (levelOfRank ∘ v) ⊆ A}` is increasing and its preimage under
`r` is `roundedSet Λ N ∅ A`. If `K` witnesses `A` at `ω`, then `K` witnesses the chain set at `r ω`:
a point above the rounded values on `K` is above `ω` on `K`, and `A` is increasing. So
`A □ B ⊆ r ⁻¹' (A_N □ B_N)` exactly, with no limit and no measurability of `A □ B`.

Step 2. Induction over the set `s` of coordinates that are not rounded, with the claim
`P[A □ B] ≤ P[roundedSet Λ N s A] P[roundedSet Λ N s B]` for every `N`. From `s` to `insert k s`
let the number of levels of coordinate `k` tend to infinity in both factors. For `s = univ` the
right side is `P[A] P[B]`.

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985), Theorem 3.3.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace ProbabilityBasics.BK

section Chains

variable {ι : Type*} {E : ι → Type*} [∀ i, LinearOrder (E i)]

/-- The event `A` seen on the chain of ranks: the rank vectors `v` for which every point at or
above the levels of `v` lies in `A` (the set `A_N` of Step 1). -/
private def chainSet (Λ : ∀ i, Finset (E i)) (A : Set (∀ i, E i)) :
    Set (∀ i, Fin ((Λ i).card + 1)) :=
  {v | boxAbove (fun i => levelOfRank (Λ i) (v i)) ⊆ A}

/-- The chain set of any event is increasing: larger ranks give larger levels, hence a smaller box
(Step 1). -/
private theorem isUpperSet_chainSet (Λ : ∀ i, Finset (E i)) (A : Set (∀ i, E i)) :
    IsUpperSet (chainSet Λ A) :=
  fun _ _ hv hmem => Set.Subset.trans
    (boxAbove_anti fun i => (levelOfRank_strictMono (Λ i)).monotone (hv i)) hmem

/-- A witness for `A` at `ω` is a witness for the chain set at the rank vector of `ω`: a point above
the rounded values on `K` is above `ω` on `K`, and `A` is increasing. -/
private theorem isWitnessSet_chainSet (Λ : ∀ i, Finset (E i)) {A : Set (∀ i, E i)}
    (hA : IsUpperSet A) {K : Set ι} {ω : ∀ i, E i} (hK : IsWitnessSet A K ω) :
    IsWitnessSet (chainSet Λ A) K (fun i => rankUp (Λ i) (ω i)) := by
  classical
  have hK' : agreementCylinder K ω ⊆ A := hK
  intro v hv ω' hω'
  -- the point equal to `ω` on `K` and to `ω'` elsewhere
  let ζ : ∀ i, E i := fun i => if i ∈ K then ω i else ω' i
  have hζA : ζ ∈ A := hK' fun i hi => by simp [ζ, hi]
  have hζω' : ζ ≤ ω' := by
    intro i
    by_cases hi : i ∈ K
    · have h1 := mem_boxAbove.1 hω' i
      rw [show v i = rankUp (Λ i) (ω i) from hv i hi, levelOfRank_rankUp] at h1
      simp only [ζ, hi, ↓reduceIte]
      exact WithTop.coe_le_coe.1 ((le_roundUp _ _).trans h1)
    · simp [ζ, hi]
  exact hA hζω' hζA

/-- Step 1, exact inclusion: the box occurrence of two increasing events lies in the preimage of the
box occurrence of their chain sets under the rank map. -/
private theorem boxOccurrence_subset_rank_preimage (Λ : ∀ i, Finset (E i)) {A B : Set (∀ i, E i)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    boxOccurrence A B ⊆
      (fun ω i => rankUp (Λ i) (ω i)) ⁻¹' boxOccurrence (chainSet Λ A) (chainSet Λ B) := by
  rintro ω ⟨K, L, hKL, hK, hL⟩
  exact ⟨K, L, hKL, isWitnessSet_chainSet Λ hA hK, isWitnessSet_chainSet Λ hB hL⟩

/-- With every coordinate rounded, the rounded set is the preimage of the chain set under the rank
map: `r ⁻¹' A_N = roundedSet Λ N ∅ A`. -/
private theorem rank_preimage_chainSet [DecidableEq ι] (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ)
    (A : Set (∀ i, E i)) :
    (fun ω i => rankUp (Λ i (N i)) (ω i)) ⁻¹' chainSet (fun i => Λ i (N i)) A =
      roundedSet Λ N ∅ A := by
  ext ω
  have hρ : (fun i => if i ∈ (∅ : Finset ι) then (ω i : WithTop (E i))
      else roundUp (Λ i (N i)) (ω i)) =
      fun i => levelOfRank (Λ i (N i)) (rankUp (Λ i (N i)) (ω i)) := by
    funext i
    simp [levelOfRank_rankUp]
  show boxAbove (fun i => levelOfRank (Λ i (N i)) (rankUp (Λ i (N i)) (ω i))) ⊆ A ↔
    boxAbove (fun i => if i ∈ (∅ : Finset ι) then (ω i : WithTop (E i))
      else roundUp (Λ i (N i)) (ω i)) ⊆ A
  rw [hρ]

end Chains

section Step1

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, OrderTopology (E i)] [∀ i, BorelSpace (E i)]
  (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- The BK inequality for the rank map: the preimage of a box occurrence of increasing chain events
under the ranks among finitely many levels per coordinate (Step 1). It is `bk_fin_chains` with the
laws `(μ i).map (rankUp (Λ i))`. -/
private theorem bk_rank_preimage (Λ : ∀ i, Finset (E i))
    {A B : Set (∀ i, Fin ((Λ i).card + 1))} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    Measure.pi μ ((fun ω i => rankUp (Λ i) (ω i)) ⁻¹' boxOccurrence A B) ≤
      Measure.pi μ ((fun ω i => rankUp (Λ i) (ω i)) ⁻¹' A) *
        Measure.pi μ ((fun ω i => rankUp (Λ i) (ω i)) ⁻¹' B) := by
  have hr : Measurable (fun (ω : ∀ i, E i) i => rankUp (Λ i) (ω i)) :=
    measurable_pi_iff.mpr fun i => (measurable_rankUp (Λ i)).comp (measurable_pi_apply i)
  have hmap : (Measure.pi μ).map (fun (ω : ∀ i, E i) i => rankUp (Λ i) (ω i)) =
      Measure.pi (fun i => (μ i).map (rankUp (Λ i))) :=
    Measure.pi_map_pi (fun i => (measurable_rankUp (Λ i)).aemeasurable)
  have hpre : ∀ S : Set (∀ i, Fin ((Λ i).card + 1)),
      Measure.pi μ ((fun (ω : ∀ i, E i) i => rankUp (Λ i) (ω i)) ⁻¹' S) =
        Measure.pi (fun i => (μ i).map (rankUp (Λ i))) S := fun S => by
    rw [← hmap, Measure.map_apply hr MeasurableSet.of_discrete]
  have : ∀ i, IsProbabilityMeasure ((μ i).map (rankUp (Λ i))) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (measurable_rankUp (Λ i)).aemeasurable).mpr inferInstance
  rw [hpre, hpre, hpre]
  exact bk_fin_chains (k := fun i => (Λ i).card) (fun i => (μ i).map (rankUp (Λ i))) hA hB

variable [DecidableEq ι]

/-- **Step 1: rounding up to finitely many levels.** With every coordinate rounded up to the levels
`Λ i (N i)`, `P[A □ B] ≤ P[roundedSet Λ N ∅ A] P[roundedSet Λ N ∅ B]` for increasing `A` and `B`.
The inclusion `A □ B ⊆ r ⁻¹' (A_N □ B_N)` is exact, so only monotonicity of the outer measure is
used: neither `A □ B` nor `A` and `B` need to be measurable. Beyond the paper. -/
theorem bk_roundedSet_empty (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ) {A B : Set (∀ i, E i)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    Measure.pi μ (boxOccurrence A B) ≤
      Measure.pi μ (roundedSet Λ N ∅ A) * Measure.pi μ (roundedSet Λ N ∅ B) := by
  calc Measure.pi μ (boxOccurrence A B)
      ≤ Measure.pi μ ((fun ω i => rankUp (Λ i (N i)) (ω i)) ⁻¹'
          boxOccurrence (chainSet (fun i => Λ i (N i)) A) (chainSet (fun i => Λ i (N i)) B)) :=
        measure_mono (boxOccurrence_subset_rank_preimage _ hA hB)
    _ ≤ Measure.pi μ ((fun ω i => rankUp (Λ i (N i)) (ω i)) ⁻¹'
          chainSet (fun i => Λ i (N i)) A) *
        Measure.pi μ ((fun ω i => rankUp (Λ i (N i)) (ω i)) ⁻¹'
          chainSet (fun i => Λ i (N i)) B) :=
        bk_rank_preimage μ _ (isUpperSet_chainSet _ A) (isUpperSet_chainSet _ B)
    _ = Measure.pi μ (roundedSet Λ N ∅ A) * Measure.pi μ (roundedSet Λ N ∅ B) := by
        rw [rank_preimage_chainSet, rank_preimage_chainSet]

end Step1

section Step2

variable {ι : Type*} {E : ι → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
  (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Extends van den Berg and Kesten (1985), Theorem 3.3, from finite Bernoulli products to finite
products of ordered spaces. Round every coordinate up to the first `N i` levels of a level set
(Step 1), then take the coordinates off the rounding one at a time: with coordinate `k` rounded
to the first `m` levels, the measures of both rounded events tend to those with coordinate `k`
exact as `m → ∞` (`tendsto_measure_roundCoord`), and the inequality survives the limit. -/
theorem bk_inequality_pi [Fintype ι] {A B : Set (∀ i, E i)}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    Measure.pi μ (boxOccurrence A B) ≤ Measure.pi μ A * Measure.pi μ B := by
  classical
  -- level sets `D i`, enumerated by `e i`, and the finite level families `Λ i m`
  choose D hD using fun i => exists_isLevelSet (μ i)
  have hne : ∀ i, (D i).Nonempty := fun i => by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure (μ i)
    obtain ⟨d, hd, -⟩ := (hD i).coinitial x
    exact ⟨d, hd⟩
  choose e he using fun i => (hD i).countable.exists_eq_range (hne i)
  have hDe : ∀ i, IsLevelSet (μ i) (Set.range (e i)) := fun i => by
    rw [← he i]
    exact hD i
  let Λ : ∀ i, ℕ → Finset (E i) := fun i m => (Finset.range m).image (e i)
  -- Step 2a: one coordinate `k` leaves the rounding as `m → ∞`
  have hlimit : ∀ (N : ι → ℕ) {s : Finset ι} {k : ι}, k ∉ s → ∀ {C : Set (∀ i, E i)},
      MeasurableSet C → IsUpperSet C →
      Tendsto (fun m : ℕ => Measure.pi μ (roundedSet Λ (Function.update N k m) s C)) atTop
        (𝓝 (Measure.pi μ (roundedSet Λ N (insert k s) C))) := by
    intro N s k hk C hCm hC
    have h : (fun m : ℕ => Measure.pi μ (roundedSet Λ (Function.update N k m) s C)) =
        fun m : ℕ => Measure.pi μ (roundCoord k (Λ k m) (roundedSet Λ N (insert k s) C)) :=
      funext fun m => by rw [roundedSet_update Λ N hk m C]
    rw [h]
    exact tendsto_measure_roundCoord μ k (Λ k) (monotone_image_range (e k)) (hDe k)
      (iUnion_image_range (e k)) (measurableSet_roundedSet Λ N _ hCm hC)
      (isUpperSet_roundedSet Λ N _ C)
  -- Step 2b: induction over the set of exact coordinates
  have key : ∀ s : Finset ι, ∀ N : ι → ℕ, Measure.pi μ (boxOccurrence A B) ≤
      Measure.pi μ (roundedSet Λ N s A) * Measure.pi μ (roundedSet Λ N s B) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun N => bk_roundedSet_empty μ Λ N hA hB
    | insert k s hk ih =>
      intro N
      exact ge_of_tendsto' (ENNReal.Tendsto.mul (hlimit N hk hAm hA)
        (Or.inr (measure_ne_top _ _)) (hlimit N hk hBm hB) (Or.inr (measure_ne_top _ _)))
        fun m => ih _
  -- Step 2c: every coordinate exact
  have hfin := key Finset.univ fun _ => 0
  rwa [roundedSet_univ _ _ hA, roundedSet_univ _ _ hB] at hfin

end Step2

end ProbabilityBasics.BK
