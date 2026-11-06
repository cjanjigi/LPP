/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Frozen.Foundations.BK.BernoulliProduct
public import ProbabilityBasics.Frozen.Foundations.BK.BoxOccurrence
public import ProbabilityBasics.Frozen.Foundations.BK.DisjointOccurrence
public import ProbabilityBasics.Frozen.Foundations.BK.VdBKDisjointOccurrence
public import ProbabilityBasics.Frozen.Foundations.Liggett.IsErgodicProcess
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettBlockProcess
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettBlockStationary
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettMomentCondition
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettRowLaws
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettSubadditive
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Named definitions for the statements of the general probability results

This file holds the short definitions that the plain-language versions of the statements use. Each
is an ordinary definition that unfolds to the expression written in the paper's words; none changes
the mathematics. The statements themselves are in `BK.lean`, `Liggett.lean` and
`Concentration.lean`.

## Main definitions

* `LPPStatements.BK.IsIncreasingEvent`, `SatisfiesBKInequality`, `SatisfiesBKFamilyInequality`: van
  den Berg and Kesten (1985), Section 3.
* `LPPStatements.BK.IsIncreasingBoolEvent`, `SatisfiesVdBKInequality`: van den Berg and Kesten
  (1985), Theorem 3.3, for the Bernoulli cube `{0,1}^n`.
* `LPPStatements.Liggett.meanRate`, `LiggettHypotheses`, `ConvergesAlmostSurely`, `ConvergesInL1`,
  `BlocksAreErgodic`: Liggett (1985), Theorem 1.10.
* `LPPStatements.Concentration.maxOfSetSums`, `IsAlmostSurelyBoundedBy`, `HasSetsOfSizeAtMost`,
  `deviationSet`, `martinConcentrationBound`: Martin (2004), Lemma 3.1.

## References

* J. van den Berg and H. Kesten, "Inequalities with applications to percolation and reliability",
  J. Appl. Probab. 22 (1985), 556-569.
* T. M. Liggett, "An improved subadditive ergodic theorem", Ann. Probab. 13 (1985), 1279-1285.
* J. B. Martin, "Limiting shape for directed percolation models", Ann. Probab. 32 (2004).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace LPPStatements.BK

open ProbabilityBasics.BK

variable {ι : Type*} {E : ι → Type*}

/-- An increasing event: a measurable set of configurations that is an upper set in the
coordinatewise order, so that raising any coordinates keeps a configuration inside the event. This
is the "increasing event" of van den Berg and Kesten (1985), Section 3, with the standing assumption
that events are measurable. -/
def IsIncreasingEvent [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)]
    (A : Set (∀ i, E i)) : Prop :=
  MeasurableSet A ∧ IsUpperSet A

/-- The inequality that, for the measure `P` on configurations, the measure of the event that `A`
and `B` occur disjointly (witnessed on disjoint finite sets of coordinates) is at most the product
`P A * P B` of their measures. Theorem 3.3 of van den Berg and Kesten (1985) states the
positive-event inequality for independent Bernoulli coordinates on `{0,1}^n`. The
ordered-coordinate result formalized here extends that inequality using the box operation of
Remark 3.5 (d); the measure of a set that is not measurable is the outer measure. -/
def SatisfiesBKInequality [∀ i, MeasurableSpace (E i)] (P : Measure (∀ i, E i))
    (A B : Set (∀ i, E i)) : Prop :=
  P (boxOccurrence A B) ≤ P A * P B

/-- The inequality for a finite family of events: the measure of the disjoint occurrence of all the
events `A j` is at most the product of their measures. This ordered-coordinate predicate extends
the family bound obtained by repeated use of the positive-event inequality in van den Berg and
Kesten (1985), Theorem 3.3, as in the proof of Corollary 3.10 (the events `E_1, ..., E_k`
occurring disjointly). Theorem 3.3 treats two events on finite independent Bernoulli
coordinates; the measure of a set that is not measurable is the outer measure. -/
def SatisfiesBKFamilyInequality [∀ i, MeasurableSpace (E i)] {J : Type*} [Fintype J]
    (P : Measure (∀ i, E i)) (A : J → Set (∀ i, E i)) : Prop :=
  P (disjointOccurrence A) ≤ ∏ j, P (A j)

/-- An increasing event on the Bernoulli cube `{0,1}^n` (configurations `Fin n → Bool`, with
`false < true`): a set of configurations that is an upper set in the coordinatewise order, so that
switching any coordinates from `false` to `true` keeps a configuration inside the event. This is the
"increasing" (or "positive") event of van den Berg and Kesten (1985), Section 3. -/
def IsIncreasingBoolEvent {n : ℕ} (A : Set (Fin n → Bool)) : Prop :=
  IsUpperSet A

/-- The inequality for the Bernoulli product measure with parameters `p i = P[ω_i = 1]`: the
probability that `A` and `B` occur disjointly (the set `vdBKDisjointOccurrence A B`) is at most the
product of the probabilities of `A` and `B`. Van den Berg and Kesten (1985), Theorem 3.3, inequality
(3.4). -/
def SatisfiesVdBKInequality {n : ℕ} (p : Fin n → unitInterval) (A B : Set (Fin n → Bool)) : Prop :=
  bernoulliProduct p (vdBKDisjointOccurrence A B) ≤ bernoulliProduct p A * bernoulliProduct p B

end LPPStatements.BK

namespace LPPStatements.Liggett

open ProbabilityBasics ProbabilityBasics.Liggett

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The mean rate `(1/n) E X_{0,n}`, the quantity whose limit and infimum appear in Liggett (1985),
(1.4). -/
noncomputable def meanRate (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) (n : ℕ) : ℝ :=
  (∫ ω, X 0 n ω ∂μ) / n

/-- The four hypotheses of Liggett (1985), Theorem 1.10, for a doubly indexed family `X m n` of
random variables under the probability measure `μ`:
* `subadditive`: (1.7), `X_{0,n} ≤ X_{0,m} + X_{m,n}` for `0 < m < n`, almost surely;
* `row_laws`: (1.8), the process `{X_{m+1,m+k+1}, k ≥ 1}` has the same joint law as
  `{X_{m,m+k}, k ≥ 1}`;
* `block_stationary`: (1.9), for each `k ≥ 1` the block process `{X_{nk,(n+1)k}, n ≥ 1}` is
  stationary;
* `moment_condition`: (1.3), `E|X_{0,n}| < ∞` and `E X_{0,n} ≥ -c n` for one constant `c`. -/
structure LiggettHypotheses (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) : Prop where
  /-- Hypothesis (1.7). -/
  subadditive : LiggettSubadditive μ X
  /-- Hypothesis (1.8). -/
  row_laws : LiggettRowLaws μ X
  /-- Hypothesis (1.9). -/
  block_stationary : LiggettBlockStationary μ X
  /-- Hypothesis (1.3). -/
  moment_condition : LiggettMomentCondition μ X

/-- The conclusion (1.5) of Liggett (1985), Theorem 1.10, almost surely: `X_{0,n}/n` converges to
`Xlim ω` for almost every `ω`. -/
def ConvergesAlmostSurely (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) (Xlim : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => X 0 n ω / n) atTop (𝓝 (Xlim ω))

/-- The conclusion (1.5) of Liggett (1985), Theorem 1.10, in `L¹`: `E |X_{0,n}/n - Xlim|` tends to
`0`. -/
def ConvergesInL1 (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) (Xlim : Ω → ℝ) : Prop :=
  Tendsto (fun n : ℕ => ∫ ω, |X 0 n ω / n - Xlim ω| ∂μ) atTop (𝓝 0)

/-- The ergodicity assumption of the last sentence of Liggett (1985), Theorem 1.10: the stationary
processes of (1.9), the block processes `{X_{nk,(n+1)k}, n ≥ 1}` for `k ≥ 1`, are ergodic. -/
def BlocksAreErgodic (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → IsErgodicProcess μ (liggettBlockProcess X k)

end LPPStatements.Liggett

namespace LPPStatements.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*}

/-- The maximum `Z` over the sets `c` in the nonempty family `C` of the sums `∑ i ∈ c, Y i`: the
maximum of set sums of Martin (2004), Lemma 3.1. -/
def maxOfSetSums (C : Finset (Finset ι)) (hC : C.Nonempty) (Y : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  C.sup' hC (fun c => ∑ i ∈ c, Y i ω)

/-- Every `Y i` is bounded by `L` in absolute value almost surely: the hypothesis `|Y_i| ≤ L` of
Martin (2004), Lemma 3.1. -/
def IsAlmostSurelyBoundedBy (P : Measure Ω) (Y : ι → Ω → ℝ) (L : ℝ) : Prop :=
  ∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ L

/-- Every set of the family `C` has at most `R` elements: the size hypothesis of Martin (2004),
Lemma 3.1. -/
def HasSetsOfSizeAtMost (C : Finset (Finset ι)) (R : ℕ) : Prop :=
  ∀ c ∈ C, c.card ≤ R

/-- The deviation event `{|Z - E Z| ≥ u}` of the random variable `Z` under the measure `P`. -/
def deviationSet (P : Measure Ω) (Z : Ω → ℝ) (u : ℝ) : Set Ω :=
  {ω | u ≤ |Z ω - ∫ η, Z η ∂P|}

/-- The bound `exp (64 - u² / (64 R L²))` printed in Martin (2004), Lemma 3.1 (with Lean's
convention that division by zero is zero). -/
noncomputable def martinConcentrationBound (R : ℕ) (L u : ℝ) : ℝ :=
  Real.exp (64 - u ^ 2 / (64 * R * L ^ 2))

end LPPStatements.Concentration
