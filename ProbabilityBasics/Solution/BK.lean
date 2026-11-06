/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Statements.BK

/-!
# Solution: the van den Berg–Kesten inequalities

The five statements below include Theorem 3.3 on the Bernoulli cube and its finite-family and
ordered-space extensions. The definitions and theorem statements match the Challenge byte for byte; each proof applies the Statements library.

## Main results

- `bk_inequality`
- `bk_inequality_family`
- `bk_inequality_countable`
- `bk_inequality_family_countable`
- `bk_inequality_bernoulli_cube`

## References

- J. van den Berg and H. Kesten, "Inequalities with applications to percolation and reliability",
  J. Appl. Probab. 22 (1985), 556–569, Theorem 3.3 and the proof of Corollary 3.10.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LPPAudit.BK

/-- van den Berg–Kesten's cylinder `C(K, ω)`: the configurations that agree
with `ω` at every coordinate in `K`. -/
def agreementCylinder {ι : Type*} {E : ι → Type*} (K : Set ι) (ω : ∀ i, E i) : Set (∀ i, E i) :=
  {ω' | ∀ i ∈ K, ω' i = ω i}

/-- The coordinates in `K` witness the event `A` at `ω`: every configuration
that agrees with `ω` on `K` lies in `A`. -/
def IsWitnessSet {ι : Type*} {E : ι → Type*} (A : Set (∀ i, E i)) (K : Set ι) (ω : ∀ i, E i) : Prop :=
  agreementCylinder K ω ⊆ A

/-- Disjoint occurrence `A □ B`: two disjoint finite sets of coordinates
witness `A` and `B` respectively. -/
def boxOccurrence {ι : Type*} {E : ι → Type*} (A B : Set (∀ i, E i)) : Set (∀ i, E i) :=
  {ω | ∃ K L : Finset ι, Disjoint K L ∧
    IsWitnessSet A (K : Set ι) ω ∧ IsWitnessSet B (L : Set ι) ω}

/-- Disjoint occurrence of a family `A j`: pairwise disjoint finite sets of
coordinates witness the events `A j` respectively. -/
def disjointOccurrence {ι : Type*} {E : ι → Type*} {J : Type*} (A : J → Set (∀ i, E i)) : Set (∀ i, E i) :=
  {ω | ∃ K : J → Finset ι, Pairwise (fun j l => Disjoint (K j) (K l)) ∧
    ∀ j, IsWitnessSet (A j) (K j : Set ι) ω}

/-- Independent coordinates with `P[ω_i = 1] = p i`. -/
noncomputable def bernoulliProduct {n : ℕ} (p : Fin n → unitInterval) : Measure (Fin n → Bool) :=
  Measure.pi fun i => bernoulliMeasure true false (p i)

/-- `K(ω)`: the coordinates where `ω` equals `1` (here `true`). -/
def onesOf {n : ℕ} (ω : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => ω i = true

/-- The configuration `ω'` determined by `K(ω') = K`. -/
def configOfOnes {n : ℕ} (K : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ K)

/-- The source's `A ∘ B` for increasing events (p. 562): some `K' ⊆ K(ω)` has
the configuration with ones `K'` in `A` and the configuration with ones
`K(ω) \ K'` in `B`. -/
def vdBKDisjointOccurrence {n : ℕ} (A B : Set (Fin n → Bool)) : Set (Fin n → Bool) :=
  {ω | ∃ K' ⊆ onesOf ω, configOfOnes K' ∈ A ∧ configOfOnes (onesOf ω \ K') ∈ B}

/-- An increasing event: a measurable set of configurations that is an upper set in the coordinatewise order,
so that raising any coordinates keeps a configuration inside the event. This is the "increasing event" of
van den Berg and Kesten (1985), Section 3, with the standing assumption that events are measurable. -/
def IsIncreasingEvent {ι : Type*} {E : ι → Type*} [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)]
    (A : Set (∀ i, E i)) : Prop :=
  MeasurableSet A ∧ IsUpperSet A

/-- The inequality `P[A ∘ B] ≤ P[A] P[B]` for the measure `P` on configurations: the measure of the
disjoint occurrence of `A` and `B` (witnessed on disjoint finite sets of coordinates) is at most the product
of their measures. Source: van den Berg and Kesten (1985), Theorem 3.3, with the box operation of
Remark 3.5 (d); the measure of a set that is not measurable is the outer measure. -/
def SatisfiesBKInequality {ι : Type*} {E : ι → Type*} [∀ i, MeasurableSpace (E i)] (P : Measure (∀ i, E i))
    (A B : Set (∀ i, E i)) : Prop :=
  P (boxOccurrence A B) ≤ P A * P B

/-- The inequality for a finite family of events: the measure of the disjoint occurrence of all the events
`A j` is at most the product of their measures. Source: van den Berg and Kesten (1985), the repeated use of
Theorem 3.3 in the proof of Corollary 3.10 (`E_1 ∘ ... ∘ E_k`); the measure of a set that is not measurable
is the outer measure. -/
def SatisfiesBKFamilyInequality {ι : Type*} {E : ι → Type*} [∀ i, MeasurableSpace (E i)] {J : Type*} [Fintype J]
    (P : Measure (∀ i, E i)) (A : J → Set (∀ i, E i)) : Prop :=
  P (disjointOccurrence A) ≤ ∏ j, P (A j)

/-- An increasing event on the Bernoulli cube `{0,1}^n` (configurations `Fin n → Bool`, with `false < true`): a set
of configurations that is an upper set in the coordinatewise order, so that switching any coordinates from `false`
to `true` keeps a configuration inside the event. This is the "increasing" (or "positive") event of van den Berg and
Kesten (1985), Section 3. -/
def IsIncreasingBoolEvent {n : ℕ} (A : Set (Fin n → Bool)) : Prop :=
  IsUpperSet A

/-- The inequality `P[A ∘ B] ≤ P[A] P[B]` for the Bernoulli product measure with parameters `p i = P[ω_i = 1]`:
the probability of the disjoint occurrence `A ∘ B` (the set `vdBKDisjointOccurrence A B`) is at most the product of
the probabilities of `A` and `B`. Source: van den Berg and Kesten (1985), Theorem 3.3, inequality (3.4). -/
def SatisfiesVdBKInequality {n : ℕ} (p : Fin n → unitInterval) (A B : Set (Fin n → Bool)) : Prop :=
  bernoulliProduct p (vdBKDisjointOccurrence A B) ≤ bernoulliProduct p A * bernoulliProduct p B

/-- The challenge definition agrees with the corresponding library definition. -/
theorem agreementCylinder_eq {ι : Type*} {E : ι → Type*} (K : Set ι) (ω : ∀ i, E i) :
    agreementCylinder K ω = ProbabilityBasics.BK.agreementCylinder K ω := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem IsWitnessSet_eq {ι : Type*} {E : ι → Type*} (A : Set (∀ i, E i)) (K : Set ι) (ω : ∀ i, E i) :
    IsWitnessSet A K ω = ProbabilityBasics.BK.IsWitnessSet A K ω := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem boxOccurrence_eq {ι : Type*} {E : ι → Type*} (A B : Set (∀ i, E i)) :
    boxOccurrence A B = ProbabilityBasics.BK.boxOccurrence A B := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem disjointOccurrence_eq {ι : Type*} {E : ι → Type*} {J : Type*} (A : J → Set (∀ i, E i)) :
    disjointOccurrence A = ProbabilityBasics.BK.disjointOccurrence A := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem bernoulliProduct_eq {n : ℕ} (p : Fin n → unitInterval) :
    bernoulliProduct p = ProbabilityBasics.BK.bernoulliProduct p := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem onesOf_eq {n : ℕ} (ω : Fin n → Bool) :
    onesOf ω = ProbabilityBasics.BK.onesOf ω := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem configOfOnes_eq {n : ℕ} (K : Finset (Fin n)) :
    configOfOnes K = ProbabilityBasics.BK.configOfOnes K := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem vdBKDisjointOccurrence_eq {n : ℕ} (A B : Set (Fin n → Bool)) :
    vdBKDisjointOccurrence A B = ProbabilityBasics.BK.vdBKDisjointOccurrence A B := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem IsIncreasingEvent_eq {ι : Type*} {E : ι → Type*} [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)]
    (A : Set (∀ i, E i)) :
    IsIncreasingEvent A = LPPStatements.BK.IsIncreasingEvent A := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem SatisfiesBKInequality_eq {ι : Type*} {E : ι → Type*} [∀ i, MeasurableSpace (E i)] (P : Measure (∀ i, E i))
    (A B : Set (∀ i, E i)) :
    SatisfiesBKInequality P A B = LPPStatements.BK.SatisfiesBKInequality P A B := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem SatisfiesBKFamilyInequality_eq {ι : Type*} {E : ι → Type*} [∀ i, MeasurableSpace (E i)] {J : Type*} [Fintype J]
    (P : Measure (∀ i, E i)) (A : J → Set (∀ i, E i)) :
    SatisfiesBKFamilyInequality P A = LPPStatements.BK.SatisfiesBKFamilyInequality P A := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem IsIncreasingBoolEvent_eq {n : ℕ} (A : Set (Fin n → Bool)) :
    IsIncreasingBoolEvent A = LPPStatements.BK.IsIncreasingBoolEvent A := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem SatisfiesVdBKInequality_eq {n : ℕ} (p : Fin n → unitInterval) (A B : Set (Fin n → Bool)) :
    SatisfiesVdBKInequality p A B = LPPStatements.BK.SatisfiesVdBKInequality p A B := rfl

/-- Extends van den Berg and Kesten (1985), Theorem 3.3, from {0,1}^n to finite products of ordered spaces.

For two increasing events `A` and `B` on a finite product of totally ordered spaces `E i`, each with a second
countable order topology, its Borel σ-algebra and an arbitrary probability measure `μ i`, the product measure
of the disjoint occurrence of `A` and `B` is at most the product of their measures. This is Theorem 3.3 of the
paper, which treats `{0,1}^n` with independent Bernoulli coordinates, stated with the box operation of its
Remark 3.5 (d) (disjoint finite sets of coordinates witness `A` and `B`). -/
theorem bk_inequality {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    [Fintype ι] {A B : Set (∀ i, E i)} (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    SatisfiesBKInequality (Measure.pi μ) A B :=
  LPPStatements.BK.bk_inequality μ hA hB

/-- Extends van den Berg and Kesten (1985), Theorem 3.3, to a finite family of events on finite products of ordered spaces.

For a finite family of increasing events `A j`, `j` in a finite index type, on a finite product of totally ordered spaces with
arbitrary probability measures, the product measure of the disjoint occurrence of all the `A j` is at most the
product of their measures. In the paper this is the inequality `P[E_1 ∘ ... ∘ E_k] ≤ P[E_1] ... P[E_k]` obtained
from Theorem 3.3 by induction over the family in the proof of Corollary 3.10. -/
theorem bk_inequality_family {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    [Fintype ι] {J : Type*} [Fintype J] {A : J → Set (∀ i, E i)}
    (hA : ∀ j, IsIncreasingEvent (A j)) :
    SatisfiesBKFamilyInequality (Measure.pi μ) A :=
  LPPStatements.BK.bk_inequality_family μ hA

/-- Extends van den Berg and Kesten (1985), Theorem 3.3, to countable products of ordered spaces.

For two increasing events `A` and `B` on a countable product of totally ordered spaces with arbitrary probability
measures, the infinite product measure of the disjoint occurrence of `A` and `B` is at most the product of
their measures. When the disjoint occurrence is not measurable, the left side is the outer measure. The paper
proves Theorem 3.3 for finitely many Bernoulli coordinates and reduces infinite graphs to finite ones in the
proof of Corollary 3.10 only by "obvious limit arguments". -/
theorem bk_inequality_countable {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    [Countable ι] {A B : Set (∀ i, E i)} (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    SatisfiesBKInequality (Measure.infinitePi μ) A B :=
  LPPStatements.BK.bk_inequality_countable μ hA hB

/-- Extends van den Berg and Kesten (1985), Theorem 3.3, to a finite family of events on countable products of ordered spaces.

For a finite family of increasing events `A j`, `j` in a finite index type, on a countable product of totally ordered spaces with
arbitrary probability measures, the infinite product measure of the disjoint occurrence of all the `A j` is at
most the product of their measures. When the disjoint occurrence is not measurable, the left side is the outer
measure. -/
theorem bk_inequality_family_countable {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    [Countable ι] {J : Type*} [Fintype J] {A : J → Set (∀ i, E i)}
    (hA : ∀ j, IsIncreasingEvent (A j)) :
    SatisfiesBKFamilyInequality (Measure.infinitePi μ) A :=
  LPPStatements.BK.bk_inequality_family_countable μ hA

/-- van den Berg and Kesten (1985), Theorem 3.3.

For two increasing events `A` and `B` in `{0,1}^n`, with independent Bernoulli coordinates `P[ω_i = 1] = p i`,
the probability of the disjoint occurrence `A ∘ B` is at most `P[A] P[B]`: inequality (3.4) of the paper, with
`A ∘ B` as defined on page 562. -/
theorem bk_inequality_bernoulli_cube {n : ℕ} (p : Fin n → unitInterval) {A B : Set (Fin n → Bool)}
    (hA : IsIncreasingBoolEvent A) (hB : IsIncreasingBoolEvent B) :
    SatisfiesVdBKInequality p A B :=
  LPPStatements.BK.bk_inequality_bernoulli_cube p hA hB

end LPPAudit.BK
