/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.CloseBadPairSourceBound
public import Differentiability.Probability.ForwardBadBoxAvoidance
public import Differentiability.Probability.FiniteBadCountFamily

import Mathlib.Tactic

/-!
# The joint finite event for backward heavy attachments

Compose the three strict lower-tail events on the actual environment law. The
geometric construction of their finite regions and the attachment paths are
separate results.
-/

public section

open MeasureTheory Set

namespace LPPDifferentiability

/-- The same three finite source events are jointly measurable and have the
sum-of-failures lower bound. No disjointness is assumed between the target,
net, or tube sites. -/
theorem measurable_and_measureReal_backward_heavy_attachment_event_ge
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (Q J N : Finset Lattice)
    (Sigma : {u : Lattice // u ∈ J} → Finset Lattice)
    (K L A : ℕ)
    (hCap : ∀ u : {u : Lattice // u ∈ J}, (Sigma u).card ≤ A) :
    let pairFailure : Set Environment := ⋃ uv ∈
      (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
        |(uv.1.1 : ℝ) - (uv.2.1 : ℝ)| + |(uv.1.2 : ℝ) - (uv.2.2 : ℝ)| ≤ 2),
      {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}
    let boxSafe : Set Environment := {ω : Environment | ∀ z ∈
      J ∪ N.biUnion (fun w : Lattice =>
        Finset.Icc w.1 (w.1 + (L : ℤ)) ×ˢ
          Finset.Icc w.2 (w.2 + (L : ℤ))),
      -T ≤ ω z}
    let countFailure : Set Environment := {ω : Environment | ∃ u ∈ J.attach,
      K ≤ ((Sigma u).filter (fun z => ω z < -T)).card}
    let good := pairFailureᶜ ∩ boxSafe ∩ countFailureᶜ
    MeasurableSet good ∧
      (environmentLaw μ).real good ≥
        1 - (12 * (Q.card : ℝ) * (μ.real (Iio (-T))) ^ 2 +
          ((J.card + N.card * (L + 1) ^ 2 : ℕ) : ℝ) * μ.real (Iio (-T)) +
          (J.card : ℝ) * ((A : ℝ) * μ.real (Iio (-T))) ^ K) := by
  classical
  dsimp only
  let pairFailure : Set Environment := ⋃ uv ∈
    (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
      |(uv.1.1 : ℝ) - (uv.2.1 : ℝ)| + |(uv.1.2 : ℝ) - (uv.2.2 : ℝ)| ≤ 2),
    {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}
  let boxSafe : Set Environment := {ω : Environment | ∀ z ∈
    J ∪ N.biUnion (fun w : Lattice =>
      Finset.Icc w.1 (w.1 + (L : ℤ)) ×ˢ
        Finset.Icc w.2 (w.2 + (L : ℤ))),
    -T ≤ ω z}
  let countFailure : Set Environment := {ω : Environment | ∃ u ∈ J.attach,
    K ≤ ((Sigma u).filter (fun z => ω z < -T)).card}
  let good := pairFailureᶜ ∩ boxSafe ∩ countFailureᶜ
  change MeasurableSet good ∧
    (environmentLaw μ).real good ≥
      1 - (12 * (Q.card : ℝ) * (μ.real (Iio (-T))) ^ 2 +
        ((J.card + N.card * (L + 1) ^ 2 : ℕ) : ℝ) * μ.real (Iio (-T)) +
        (J.card : ℝ) * ((A : ℝ) * μ.real (Iio (-T))) ^ K)
  have hPairMeas : MeasurableSet pairFailure :=
    measurableSet_close_bad_pair_union Q T
  have hPairProb : (environmentLaw μ).real pairFailure ≤
      12 * (Q.card : ℝ) * (μ.real (Iio (-T))) ^ 2 :=
    environmentLaw_real_close_bad_pair_le_twelve μ Q T
  have hBox := measureReal_positive_bad_box_avoidance_ge μ T J N L
  have hBoxMeas : MeasurableSet boxSafe := hBox.1
  have hBoxProb : (environmentLaw μ).real boxSafe ≥
      1 - ((J.card + N.card * (L + 1) ^ 2 : ℕ) : ℝ) *
        μ.real (Iio (-T)) := hBox.2
  have hCount :=
    measurable_and_measureReal_exists_bad_count_ge_le μ T J.attach Sigma A K
      (fun u _ => hCap u)
  have hCountMeas : MeasurableSet countFailure := hCount.1
  have hCountProb : (environmentLaw μ).real countFailure ≤
      (J.card : ℝ) * ((A : ℝ) * μ.real (Iio (-T))) ^ K := by
    simpa only [Finset.card_attach] using hCount.2
  have hGoodMeas : MeasurableSet good := by
    exact (hPairMeas.compl.inter hBoxMeas).inter hCountMeas.compl
  have hGoodCompl : goodᶜ = pairFailure ∪ boxSafeᶜ ∪ countFailure := by
    ext ω
    simp only [good, mem_compl_iff, mem_inter_iff, mem_union]
    tauto
  have hFailureProb : (environmentLaw μ).real goodᶜ ≤
      12 * (Q.card : ℝ) * (μ.real (Iio (-T))) ^ 2 +
        ((J.card + N.card * (L + 1) ^ 2 : ℕ) : ℝ) * μ.real (Iio (-T)) +
        (J.card : ℝ) * ((A : ℝ) * μ.real (Iio (-T))) ^ K := by
    rw [hGoodCompl]
    calc
      (environmentLaw μ).real (pairFailure ∪ boxSafeᶜ ∪ countFailure) ≤
          (environmentLaw μ).real (pairFailure ∪ boxSafeᶜ) +
            (environmentLaw μ).real countFailure := measureReal_union_le _ _
      _ ≤ ((environmentLaw μ).real pairFailure +
            (environmentLaw μ).real boxSafeᶜ) +
            (environmentLaw μ).real countFailure :=
        add_le_add (measureReal_union_le pairFailure boxSafeᶜ) le_rfl
      _ ≤ _ := by
        rw [probReal_compl_eq_one_sub (μ := environmentLaw μ) hBoxMeas]
        linarith only [hPairProb, hBoxProb, hCountProb]
  have hGoodProb : (environmentLaw μ).real good ≥
      1 - (12 * (Q.card : ℝ) * (μ.real (Iio (-T))) ^ 2 +
        ((J.card + N.card * (L + 1) ^ 2 : ℕ) : ℝ) * μ.real (Iio (-T)) +
        (J.card : ℝ) * ((A : ℝ) * μ.real (Iio (-T))) ^ K) := by
    rw [probReal_compl_eq_one_sub (μ := environmentLaw μ) hGoodMeas] at hFailureProb
    linarith only [hFailureProb]
  exact ⟨hGoodMeas, hGoodProb⟩

/-- Conditional source-scale form of the finite-event estimate. The displayed
caps are hypotheses from finite geometry; this theorem does not construct the
regions or prove the full attachment lemma. -/
private theorem backward_heavy_attachment_event_ge_of_finite_caps
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (Q J N : Finset Lattice)
    (Sigma : {u : Lattice // u ∈ J} → Finset Lattice)
    (K L m : ℕ) (D s B : ℝ)
    (hD : 1 ≤ D) (hs : 0 ≤ s) (hB : 0 ≤ B)
    (hQ : (Q.card : ℝ) ≤ 4 * D * s ^ 2)
    (hJ : (J.card : ℝ) ≤ D * s + 1)
    (hN : (N.card : ℝ) ≤ B)
    (hCap : ∀ u : {u : Lattice // u ∈ J},
      (Sigma u).card ≤ (2 * K + 5) * (m + 1)) :
    let pairFailure : Set Environment := ⋃ uv ∈
      (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
        |(uv.1.1 : ℝ) - (uv.2.1 : ℝ)| + |(uv.1.2 : ℝ) - (uv.2.2 : ℝ)| ≤ 2),
      {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}
    let boxSafe : Set Environment := {ω : Environment | ∀ z ∈
      J ∪ N.biUnion (fun w : Lattice =>
        Finset.Icc w.1 (w.1 + (L : ℤ)) ×ˢ
          Finset.Icc w.2 (w.2 + (L : ℤ))),
      -T ≤ ω z}
    let countFailure : Set Environment := {ω : Environment | ∃ u ∈ J.attach,
      K ≤ ((Sigma u).filter (fun z => ω z < -T)).card}
    let good := pairFailureᶜ ∩ boxSafe ∩ countFailureᶜ
    (environmentLaw μ).real good ≥
      1 - (48 * D * s ^ 2 * (μ.real (Iio (-T))) ^ 2 +
        (D * s + 1 + B * (((L + 1 : ℕ) : ℝ) ^ 2)) * μ.real (Iio (-T)) +
        (D * s + 1) *
          ((((2 * K + 5) * (m + 1) : ℕ) : ℝ) * μ.real (Iio (-T))) ^ K) := by
  classical
  dsimp only
  let pairFailure : Set Environment := ⋃ uv ∈
    (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
      |(uv.1.1 : ℝ) - (uv.2.1 : ℝ)| + |(uv.1.2 : ℝ) - (uv.2.2 : ℝ)| ≤ 2),
    {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}
  let boxSafe : Set Environment := {ω : Environment | ∀ z ∈
    J ∪ N.biUnion (fun w : Lattice =>
      Finset.Icc w.1 (w.1 + (L : ℤ)) ×ˢ
        Finset.Icc w.2 (w.2 + (L : ℤ))),
    -T ≤ ω z}
  let countFailure : Set Environment := {ω : Environment | ∃ u ∈ J.attach,
    K ≤ ((Sigma u).filter (fun z => ω z < -T)).card}
  let good := pairFailureᶜ ∩ boxSafe ∩ countFailureᶜ
  change (environmentLaw μ).real good ≥
    1 - (48 * D * s ^ 2 * (μ.real (Iio (-T))) ^ 2 +
      (D * s + 1 + B * (((L + 1 : ℕ) : ℝ) ^ 2)) * μ.real (Iio (-T)) +
      (D * s + 1) *
        ((((2 * K + 5) * (m + 1) : ℕ) : ℝ) * μ.real (Iio (-T))) ^ K)
  let pT : ℝ := μ.real (Iio (-T))
  have hpT : 0 ≤ pT := measureReal_nonneg
  have hGeneric :=
    measurable_and_measureReal_backward_heavy_attachment_event_ge μ T Q J N Sigma K L
      ((2 * K + 5) * (m + 1)) hCap
  have hGenericProb : (environmentLaw μ).real good ≥
      1 - (12 * (Q.card : ℝ) * pT ^ 2 +
        ((J.card + N.card * (L + 1) ^ 2 : ℕ) : ℝ) * pT +
        (J.card : ℝ) *
          ((((2 * K + 5) * (m + 1) : ℕ) : ℝ) * pT) ^ K) := by
    simpa only [pT] using hGeneric.2
  have hPairCap : 12 * (Q.card : ℝ) * pT ^ 2 ≤
      48 * D * s ^ 2 * pT ^ 2 := by
    calc
      12 * (Q.card : ℝ) * pT ^ 2 = (12 * (Q.card : ℝ)) * pT ^ 2 := by ring
      _ ≤ (12 * (4 * D * s ^ 2)) * pT ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hQ (by norm_num)) (sq_nonneg pT)
      _ = 48 * D * s ^ 2 * pT ^ 2 := by ring
  have hBoxCard : ((J.card + N.card * (L + 1) ^ 2 : ℕ) : ℝ) ≤
      D * s + 1 + B * (((L + 1 : ℕ) : ℝ) ^ 2) := by
    calc
      ((J.card + N.card * (L + 1) ^ 2 : ℕ) : ℝ) =
          (J.card : ℝ) + (N.card : ℝ) * (((L + 1 : ℕ) : ℝ) ^ 2) := by
        push_cast
        ring
      _ ≤ D * s + 1 + B * (((L + 1 : ℕ) : ℝ) ^ 2) := by
        exact add_le_add hJ
          (mul_le_mul_of_nonneg_right hN (sq_nonneg ((L + 1 : ℕ) : ℝ)))
  have hBoxCap :
      ((J.card + N.card * (L + 1) ^ 2 : ℕ) : ℝ) * pT ≤
        (D * s + 1 + B * (((L + 1 : ℕ) : ℝ) ^ 2)) * pT :=
    mul_le_mul_of_nonneg_right hBoxCard hpT
  have hCountPower :
      0 ≤ ((((2 * K + 5) * (m + 1) : ℕ) : ℝ) * pT) ^ K :=
    pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hpT) K
  have hCountCap : (J.card : ℝ) *
        ((((2 * K + 5) * (m + 1) : ℕ) : ℝ) * pT) ^ K ≤
      (D * s + 1) *
        ((((2 * K + 5) * (m + 1) : ℕ) : ℝ) * pT) ^ K :=
    mul_le_mul_of_nonneg_right hJ hCountPower
  have hTotalCap :
      12 * (Q.card : ℝ) * pT ^ 2 +
        ((J.card + N.card * (L + 1) ^ 2 : ℕ) : ℝ) * pT +
        (J.card : ℝ) *
          ((((2 * K + 5) * (m + 1) : ℕ) : ℝ) * pT) ^ K ≤
      48 * D * s ^ 2 * pT ^ 2 +
        (D * s + 1 + B * (((L + 1 : ℕ) : ℝ) ^ 2)) * pT +
        (D * s + 1) *
          ((((2 * K + 5) * (m + 1) : ℕ) : ℝ) * pT) ^ K := by
    exact add_le_add (add_le_add hPairCap hBoxCap) hCountCap
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hDs0 : 0 ≤ D * s := mul_nonneg hD0 hs
  have hBterm0 : 0 ≤ B * (((L + 1 : ℕ) : ℝ) ^ 2) :=
    mul_nonneg hB (sq_nonneg ((L + 1 : ℕ) : ℝ))
  have hBoxCoeff0 : 0 ≤ D * s + 1 + B * (((L + 1 : ℕ) : ℝ) ^ 2) :=
    add_nonneg (add_nonneg hDs0 (by norm_num)) hBterm0
  have hCountCoeff0 : 0 ≤ D * s + 1 := add_nonneg hDs0 (by norm_num)
  have hPairTerm0 : 0 ≤ 48 * D * s ^ 2 * pT ^ 2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD0)
      (sq_nonneg s)) (sq_nonneg pT)
  have hBoxTerm0 : 0 ≤
      (D * s + 1 + B * (((L + 1 : ℕ) : ℝ) ^ 2)) * pT :=
    mul_nonneg hBoxCoeff0 hpT
  have hCountTerm0 : 0 ≤ (D * s + 1) *
      ((((2 * K + 5) * (m + 1) : ℕ) : ℝ) * pT) ^ K :=
    mul_nonneg hCountCoeff0 hCountPower
  have hCapTotal0 : 0 ≤
      48 * D * s ^ 2 * pT ^ 2 +
        (D * s + 1 + B * (((L + 1 : ℕ) : ℝ) ^ 2)) * pT +
        (D * s + 1) *
          ((((2 * K + 5) * (m + 1) : ℕ) : ℝ) * pT) ^ K :=
    add_nonneg (add_nonneg hPairTerm0 hBoxTerm0) hCountTerm0
  rw [show μ.real (Iio (-T)) = pT from rfl]
  linarith only [hGenericProb, hTotalCap, hCapTotal0]

/-- The source-parameter version uses its actual choice `L = 4K+4` and the
corresponding inclusive positive-box cardinality `(4K+5)^2`. -/
theorem measureReal_backward_heavy_attachment_event_ge_of_source_caps
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (Q J N : Finset Lattice)
    (Sigma : {u : Lattice // u ∈ J} → Finset Lattice)
    (K m : ℕ) (D s B : ℝ)
    (hD : 1 ≤ D) (hs : 0 ≤ s) (hB : 0 ≤ B)
    (hQ : (Q.card : ℝ) ≤ 4 * D * s ^ 2)
    (hJ : (J.card : ℝ) ≤ D * s + 1)
    (hN : (N.card : ℝ) ≤ B)
    (hCap : ∀ u : {u : Lattice // u ∈ J},
      (Sigma u).card ≤ (2 * K + 5) * (m + 1)) :
    let L : ℕ := 4 * K + 4
    let pairFailure : Set Environment := ⋃ uv ∈
      (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
        |(uv.1.1 : ℝ) - (uv.2.1 : ℝ)| + |(uv.1.2 : ℝ) - (uv.2.2 : ℝ)| ≤ 2),
      {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}
    let boxSafe : Set Environment := {ω : Environment | ∀ z ∈
      J ∪ N.biUnion (fun w : Lattice =>
        Finset.Icc w.1 (w.1 + (L : ℤ)) ×ˢ
          Finset.Icc w.2 (w.2 + (L : ℤ))),
      -T ≤ ω z}
    let countFailure : Set Environment := {ω : Environment | ∃ u ∈ J.attach,
      K ≤ ((Sigma u).filter (fun z => ω z < -T)).card}
    let good := pairFailureᶜ ∩ boxSafe ∩ countFailureᶜ
    (environmentLaw μ).real good ≥
      1 - (48 * D * s ^ 2 * (μ.real (Iio (-T))) ^ 2 +
        (D * s + 1 + B * (((4 * K + 5 : ℕ) : ℝ) ^ 2)) *
          μ.real (Iio (-T)) +
        (D * s + 1) *
          ((((2 * K + 5) * (m + 1) : ℕ) : ℝ) *
            μ.real (Iio (-T))) ^ K) := by
  classical
  dsimp only
  have h := backward_heavy_attachment_event_ge_of_finite_caps
    μ T Q J N Sigma K (4 * K + 4) m D s B hD hs hB hQ hJ hN hCap
  have hBoxNat : 4 * K + 4 + 1 = 4 * K + 5 := by omega
  have hBoxReal : (((4 * K + 4 + 1 : ℕ) : ℝ) ^ 2) =
      (((4 * K + 5 : ℕ) : ℝ) ^ 2) := by
    rw [hBoxNat]
  rw [← hBoxReal]
  exact h

end LPPDifferentiability
end
