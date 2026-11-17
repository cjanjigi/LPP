/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.CanonicalHRawEnvelopes
public import Busemann.Process.CanonicalHSampleContinuity
public import Busemann.Process.CanonicalHRawSidedContinuityScalar
public import Busemann.Frozen.StrongExistence.Definitions.OneSidedLimits

import LPP_Foundations.Model.LatticeEdgeIntegration
import Mathlib.Tactic

/-! One countable canonical event carries the literal sided limits on all H tilts. -/

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology BigOperators
namespace LPP.Busemann

private theorem additive_eq_signed_edge_sums_global
    (F : Lattice → Lattice → ℝ) (hF : is_additive F) (x y : Lattice) :
    F x y =
      (if x.1 ≤ y.1 then
        ∑ k ∈ Finset.Ico x.1 y.1, F (k, x.2) ((k, x.2) + finiteEdgeStep 0)
       else
        -(∑ k ∈ Finset.Ico y.1 x.1,
          F (k, x.2) ((k, x.2) + finiteEdgeStep 0))) +
      (if x.2 ≤ y.2 then
        ∑ k ∈ Finset.Ico x.2 y.2, F (y.1, k) ((y.1, k) + finiteEdgeStep 1)
       else
        -(∑ k ∈ Finset.Ico y.2 x.2,
          F (y.1, k) ((y.1, k) + finiteEdgeStep 1))) := by
  classical
  let E : Lattice → Fin 2 → ℝ := fun z i => F z (z + finiteEdgeStep i)
  have hCurl (z : Lattice) :
      E z 0 + E (z + (1, 0)) 1 = E z 1 + E (z + (0, 1)) 0 := by
    dsimp [E, finiteEdgeStep]
    have hz₀ : z + (1, 0) + (0, 1) = z + (1, 1) := by
      ext <;> simp [Prod.mk_add_mk, add_assoc]
    have hz₁ : z + (0, 1) + (1, 0) = z + (1, 1) := by
      ext <;> simp [Prod.mk_add_mk, add_assoc]
    rw [hz₀, hz₁]
    exact (hF z (z + (1, 0)) (z + (1, 1))).trans
      (hF z (z + (0, 1)) (z + (1, 1))).symm
  obtain ⟨G, _, _, hFormula, hUnique⟩ :=
    exists_unique_lattice_edge_extension E hCurl
  have hFE (z : Lattice) :
      F z (z + (1, 0)) = E z 0 ∧ F z (z + (0, 1)) = E z 1 := by
    dsimp [E, finiteEdgeStep]
    exact ⟨rfl, rfl⟩
  have hFG : F = G := hUnique F hF hFE
  have hFormula' := hFormula x y
  rw [← hFG] at hFormula'
  simpa [E, finiteEdgeStep] using hFormula'

private theorem signed_pair_tendsto_of_edges
    (F : ℕ → Lattice → Lattice → ℝ)
    (G : Lattice → Lattice → ℝ)
    (hF : ∀ n x y, F n x y =
      (if x.1 ≤ y.1 then
        ∑ k ∈ Finset.Ico x.1 y.1, F n (k, x.2) ((k, x.2) + finiteEdgeStep 0)
       else -(∑ k ∈ Finset.Ico y.1 x.1,
          F n (k, x.2) ((k, x.2) + finiteEdgeStep 0))) +
      (if x.2 ≤ y.2 then
        ∑ k ∈ Finset.Ico x.2 y.2, F n (y.1, k) ((y.1, k) + finiteEdgeStep 1)
       else -(∑ k ∈ Finset.Ico y.2 x.2,
          F n (y.1, k) ((y.1, k) + finiteEdgeStep 1))))
    (hEdges : ∀ z i, Tendsto
      (fun n => F n z (z + finiteEdgeStep i)) atTop
      (𝓝 (G z (z + finiteEdgeStep i))))
    (x y : Lattice) :
    Tendsto (fun n => F n x y) atTop
      (𝓝 ((if x.1 ≤ y.1 then
        ∑ k ∈ Finset.Ico x.1 y.1, G (k, x.2) ((k, x.2) + finiteEdgeStep 0)
       else -(∑ k ∈ Finset.Ico y.1 x.1,
          G (k, x.2) ((k, x.2) + finiteEdgeStep 0))) +
      (if x.2 ≤ y.2 then
        ∑ k ∈ Finset.Ico x.2 y.2, G (y.1, k) ((y.1, k) + finiteEdgeStep 1)
       else -(∑ k ∈ Finset.Ico y.2 x.2,
          G (y.1, k) ((y.1, k) + finiteEdgeStep 1))))) := by
  classical
  have hHorizontal : Tendsto
      (fun n => if x.1 ≤ y.1 then
        ∑ k ∈ Finset.Ico x.1 y.1,
          F n (k, x.2) ((k, x.2) + finiteEdgeStep 0)
       else -(∑ k ∈ Finset.Ico y.1 x.1,
          F n (k, x.2) ((k, x.2) + finiteEdgeStep 0))) atTop
      (𝓝 (if x.1 ≤ y.1 then
        ∑ k ∈ Finset.Ico x.1 y.1,
          G (k, x.2) ((k, x.2) + finiteEdgeStep 0)
       else -(∑ k ∈ Finset.Ico y.1 x.1,
          G (k, x.2) ((k, x.2) + finiteEdgeStep 0)))) := by
    by_cases hxy : x.1 ≤ y.1
    · simpa [hxy] using tendsto_finsetSum _
        (fun k _ => hEdges (k, x.2) 0)
    · simpa [hxy] using (tendsto_finsetSum _
        (fun k _ => hEdges (k, x.2) 0)).neg
  have hVertical : Tendsto
      (fun n => if x.2 ≤ y.2 then
        ∑ k ∈ Finset.Ico x.2 y.2,
          F n (y.1, k) ((y.1, k) + finiteEdgeStep 1)
       else -(∑ k ∈ Finset.Ico y.2 x.2,
          F n (y.1, k) ((y.1, k) + finiteEdgeStep 1))) atTop
      (𝓝 (if x.2 ≤ y.2 then
        ∑ k ∈ Finset.Ico x.2 y.2,
          G (y.1, k) ((y.1, k) + finiteEdgeStep 1)
       else -(∑ k ∈ Finset.Ico y.2 x.2,
          G (y.1, k) ((y.1, k) + finiteEdgeStep 1)))) := by
    by_cases hxy : x.2 ≤ y.2
    · simpa [hxy] using tendsto_finsetSum _
        (fun k _ => hEdges (y.1, k) 1)
    · simpa [hxy] using (tendsto_finsetSum _
        (fun k _ => hEdges (y.1, k) 1)).neg
  have hSum := hHorizontal.add hVertical
  convert hSum using 1
  ext n
  exact hF n x y

/-- The literal countable-limit fields have one common all-H sided-limit event. -/
theorem oneSidedLimits_canonical_H_raw_fields
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (C : StrongField μ)
    (hClass : ForwardCoalescingClass μ C C)
    (hMean : MeanTilt μ C)
    (D : Set (CoalescingTilt μ)) (hD : D.Countable)
    (left right : CoalescingTilt μ → ℕ → CoalescingTilt μ)
    (hSequences : ∀ h : CoalescingTilt μ,
      (h ∈ D → left h = (fun _ => h) ∧ right h = (fun _ => h)) ∧
      (h ∉ D →
        (∀ n, left h n ∈ D ∧ (left h n).val.1 < h.val.1) ∧
        StrictMono (fun n => (left h n).val.1) ∧
        Tendsto (left h) atTop (𝓝 h) ∧
        (∀ n, right h n ∈ D ∧ h.val.1 < (right h n).val.1) ∧
        StrictAnti (fun n => (right h n).val.1) ∧
        Tendsto (right h) atTop (𝓝 h)))
    (Bm Bp : StrongField μ)
    (hRaw : ∀ h x y ω,
      Bm h x y ω = limUnder atTop (fun n => C (left h n) x y ω) ∧
      Bp h x y ω = limUnder atTop (fun n => C (right h n) x y ω)) :
    OneSidedLimits μ Bm Bp := by
  classical
  let P : Measure Environment := environmentLaw μ
  let T : Lattice → Environment → Environment :=
    fun z ω => environmentTranslationEquiv z ω
  have hGen (h : CoalescingTilt μ) :
      IsGeneralizedBusemann P T (fun ω => ω) (C h) := (hClass h).2.1
  have hCoal (h : CoalescingTilt μ) :
      HasCoalescingRightmostPaths P (C h) := (hClass h).2.2.1
  have hForward (h : CoalescingTilt μ) : IsForwardMeasurable (C h) :=
    (hClass h).2.2.2
  -- The original two means identify the invariant full tilt of each C field.
  have hTilt (h : CoalescingTilt μ) :
      ∀ᵐ ω ∂P, invariantCocycleTilt P T (fun ω => ω)
        (C h) (hGen h) ω = h.val := by
    let mEnv : MeasurableSpace Environment := inferInstance
    let I : MeasurableSpace Environment :=
      @latticeInvariantSigma Environment mEnv T
    let : MeasurableSpace Environment := mEnv
    have he := canonical_condExp_full_invariants_eq_mean μ
      (C h 0 ((1 : ℤ), (0 : ℤ))) ((hGen h).2.2 0 ((1 : ℤ), (0 : ℤ)))
    have hn := canonical_condExp_full_invariants_eq_mean μ
      (C h 0 ((0 : ℤ), (1 : ℤ))) ((hGen h).2.2 0 ((0 : ℤ), (1 : ℤ)))
    filter_upwards [he, hn] with ω heω hnω
    apply Prod.ext
    · change -(P[C h 0 ((1 : ℤ), (0 : ℤ)) | I] ω) = h.val.1
      rw [heω, (hMean h).1]
      ring
    · change -(P[C h 0 ((0 : ℤ), (1 : ℤ)) | I] ω) = h.val.2
      rw [hnω, (hMean h).2]
      ring
  have hStrict (a b : CoalescingTilt μ) (hab : a.val.1 < b.val.1) :
      ∀ᵐ ω ∂P, ∀ x : Lattice,
        C b x (x + finiteEdgeStep 0) ω ≤
          C a x (x + finiteEdgeStep 0) ω ∧
        C a x (x + finiteEdgeStep 1) ω ≤
          C b x (x + finiteEdgeStep 1) ω := by
    have h := ae_forward_coalescing_cocycle_opposite_edge_order
      μ hμ hmoment (C a) (C b) (hGen a) (hGen b)
      (hForward a) (hForward b) (hCoal a) (hCoal b)
      a.val b.val (hTilt a) (hTilt b) hab
    filter_upwards [h] with ω hω
    intro x
    simpa [finiteEdgeStep] using hω x
  have : Countable {d : CoalescingTilt μ // d ∈ D} := hD.to_subtype
  have hOrderAE : ∀ᵐ ω ∂P,
      ∀ a b : {d : CoalescingTilt μ // d ∈ D},
        a.val.val.1 < b.val.val.1 → ∀ x : Lattice,
          C b.val x (x + finiteEdgeStep 0) ω ≤
            C a.val x (x + finiteEdgeStep 0) ω ∧
          C a.val x (x + finiteEdgeStep 1) ω ≤
            C b.val x (x + finiteEdgeStep 1) ω := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    by_cases hab : a.val.val.1 < b.val.val.1
    · filter_upwards [hStrict a.val b.val hab] with ω hω
      intro _
      exact hω
    · exact Filter.Eventually.of_forall (fun _ hab' => (hab hab').elim)
  have hAddAE : ∀ᵐ ω ∂P,
      ∀ d : {h : CoalescingTilt μ // h ∈ D},
        is_additive (fun x y => C d.val x y ω) := by
    apply ae_all_iff.mpr
    intro d
    exact (hGen d.val).1.2.2
  have hSampleAE := ae_canonical_field_sided_continuous_on_countable_sample
    μ hμ hmoment C hClass hMean D hD
  filter_upwards [hOrderAE, hAddAE, hSampleAE] with ω hOrder hAdd hSample
  intro h x y
  -- The remainder is deterministic on this one countable event.
  have hLeftMem (q : CoalescingTilt μ) (n : ℕ) : left q n ∈ D := by
    by_cases hq : q ∈ D
    · rw [((hSequences q).1 hq).1]
      exact hq
    · exact ((hSequences q).2 hq).1 n |>.1
  have hRightMem (q : CoalescingTilt μ) (n : ℕ) : right q n ∈ D := by
    by_cases hq : q ∈ D
    · rw [((hSequences q).1 hq).2]
      exact hq
    · exact ((hSequences q).2 hq).2.2.2.1 n |>.1
  have hEastOrder (z : Lattice) :
      ∀ a b : CoalescingTilt μ, a ∈ D → b ∈ D →
        a.val.1 < b.val.1 →
        C b z (z + finiteEdgeStep 0) ω ≤
          C a z (z + finiteEdgeStep 0) ω := by
    intro a b ha hb hab
    exact (hOrder ⟨a, ha⟩ ⟨b, hb⟩ hab z).1
  have hNorthNegOrder (z : Lattice) :
      ∀ a b : CoalescingTilt μ, a ∈ D → b ∈ D →
        a.val.1 < b.val.1 →
        -(C b z (z + finiteEdgeStep 1) ω) ≤
          -(C a z (z + finiteEdgeStep 1) ω) := by
    intro a b ha hb hab
    exact neg_le_neg (hOrder ⟨a, ha⟩ ⟨b, hb⟩ hab z).2
  have hEastSample (z : Lattice) :
      ∀ d : CoalescingTilt μ, d ∈ D →
        (∀ hs : ℕ → CoalescingTilt μ,
          (∀ n, hs n ∈ D ∧ (hs n).val.1 < d.val.1) →
          Tendsto hs atTop (𝓝 d) →
          Tendsto (fun n => C (hs n) z (z + finiteEdgeStep 0) ω)
            atTop (𝓝 (C d z (z + finiteEdgeStep 0) ω))) ∧
        (∀ hs : ℕ → CoalescingTilt μ,
          (∀ n, hs n ∈ D ∧ d.val.1 < (hs n).val.1) →
          Tendsto hs atTop (𝓝 d) →
          Tendsto (fun n => C (hs n) z (z + finiteEdgeStep 0) ω)
            atTop (𝓝 (C d z (z + finiteEdgeStep 0) ω))) := by
    intro d hd
    exact hSample d hd z (z + finiteEdgeStep 0)
  have hNorthNegSample (z : Lattice) :
      ∀ d : CoalescingTilt μ, d ∈ D →
        (∀ hs : ℕ → CoalescingTilt μ,
          (∀ n, hs n ∈ D ∧ (hs n).val.1 < d.val.1) →
          Tendsto hs atTop (𝓝 d) →
          Tendsto (fun n => -(C (hs n) z (z + finiteEdgeStep 1) ω))
            atTop (𝓝 (-(C d z (z + finiteEdgeStep 1) ω)))) ∧
        (∀ hs : ℕ → CoalescingTilt μ,
          (∀ n, hs n ∈ D ∧ d.val.1 < (hs n).val.1) →
          Tendsto hs atTop (𝓝 d) →
          Tendsto (fun n => -(C (hs n) z (z + finiteEdgeStep 1) ω))
            atTop (𝓝 (-(C d z (z + finiteEdgeStep 1) ω)))) := by
    intro d hd
    constructor
    · intro hs hside hlim
      exact ((hSample d hd z (z + finiteEdgeStep 1)).1 hs hside hlim).neg
    · intro hs hside hlim
      exact ((hSample d hd z (z + finiteEdgeStep 1)).2 hs hside hlim).neg
  have hPositiveFiniteFromNeg (u : ℕ → ℝ)
      (hu : Tendsto (fun n => -(u n)) atTop
        (𝓝 (limUnder atTop (fun n => -(u n))))) :
      Tendsto u atTop (𝓝 (limUnder atTop u)) := by
    have hp : Tendsto u atTop
        (𝓝 (-(limUnder atTop (fun n => -(u n))))) := by
      simpa only [neg_neg] using hu.neg
    rw [hp.limUnder_eq]
    exact hp
  have hEdgeFinite (q : CoalescingTilt μ) (z : Lattice) (i : Fin 2) :
      Tendsto (fun n => C (left q n) z (z + finiteEdgeStep i) ω)
        atTop (𝓝 (Bm q z (z + finiteEdgeStep i) ω)) ∧
      Tendsto (fun n => C (right q n) z (z + finiteEdgeStep i) ω)
        atTop (𝓝 (Bp q z (z + finiteEdgeStep i) ω)) := by
    fin_cases i
    · have hf := (canonical_H_scalar_raw_limits_and_order μ D left right
          hSequences (fun d => C d z (z + finiteEdgeStep 0) ω)
          (hEastOrder z)).1 q
      have hh :
          Tendsto (fun n => C (left q n) z (z + finiteEdgeStep 0) ω) atTop
            (𝓝 (Bm q z (z + finiteEdgeStep 0) ω)) ∧
          Tendsto (fun n => C (right q n) z (z + finiteEdgeStep 0) ω) atTop
            (𝓝 (Bp q z (z + finiteEdgeStep 0) ω)) := by
        constructor
        · rw [(hRaw q z (z + finiteEdgeStep 0) ω).1]
          exact hf.1
        · rw [(hRaw q z (z + finiteEdgeStep 0) ω).2]
          exact hf.2
      simpa using hh
    · have hf := (canonical_H_scalar_raw_limits_and_order μ D left right
          hSequences (fun d => -(C d z (z + finiteEdgeStep 1) ω))
          (hNorthNegOrder z)).1 q
      have hh :
          Tendsto (fun n => C (left q n) z (z + finiteEdgeStep 1) ω) atTop
            (𝓝 (Bm q z (z + finiteEdgeStep 1) ω)) ∧
          Tendsto (fun n => C (right q n) z (z + finiteEdgeStep 1) ω) atTop
            (𝓝 (Bp q z (z + finiteEdgeStep 1) ω)) := by
        constructor
        · rw [(hRaw q z (z + finiteEdgeStep 1) ω).1]
          exact hPositiveFiniteFromNeg _ hf.1
        · rw [(hRaw q z (z + finiteEdgeStep 1) ω).2]
          exact hPositiveFiniteFromNeg _ hf.2
      simpa using hh
  have hEastCont (z : Lattice) :=
    canonical_H_scalar_raw_sided_continuity μ hμ hmoment D left right
      hSequences (fun d => C d z (z + finiteEdgeStep 0) ω)
      (hEastOrder z) (hEastSample z)
  have hNorthNegCont (z : Lattice) :=
    canonical_H_scalar_raw_sided_continuity μ hμ hmoment D left right
      hSequences (fun d => -(C d z (z + finiteEdgeStep 1) ω))
      (hNorthNegOrder z) (hNorthNegSample z)
  have hNegBm (q : CoalescingTilt μ) (z : Lattice) :
      limUnder atTop (fun n => -(C (left q n) z (z + finiteEdgeStep 1) ω)) =
        -(Bm q z (z + finiteEdgeStep 1) ω) :=
    ((hEdgeFinite q z 1).1.neg).limUnder_eq
  have hNegBp (q : CoalescingTilt μ) (z : Lattice) :
      limUnder atTop (fun n => -(C (right q n) z (z + finiteEdgeStep 1) ω)) =
        -(Bp q z (z + finiteEdgeStep 1) ω) :=
    ((hEdgeFinite q z 1).2.neg).limUnder_eq
  have hEdgeLeft (q : CoalescingTilt μ) (z : Lattice) (i : Fin 2)
      (hs : ℕ → CoalescingTilt μ)
      (hSide : ∀ n, (hs n).val.1 < q.val.1)
      (hLim : Tendsto hs atTop (𝓝 q)) :
      Tendsto (fun n => Bm (hs n) z (z + finiteEdgeStep i) ω) atTop
        (𝓝 (Bm q z (z + finiteEdgeStep i) ω)) ∧
      Tendsto (fun n => Bp (hs n) z (z + finiteEdgeStep i) ω) atTop
        (𝓝 (Bm q z (z + finiteEdgeStep i) ω)) := by
    fin_cases i
    · have hc := (hEastCont z).1 q hs hSide hLim
      have hBmSeq :
          (fun n => Bm (hs n) z (z + finiteEdgeStep 0) ω) =
          (fun n => limUnder atTop
            (fun m => C (left (hs n) m) z (z + finiteEdgeStep 0) ω)) :=
        funext fun n => (hRaw (hs n) z (z + finiteEdgeStep 0) ω).1
      have hBpSeq :
          (fun n => Bp (hs n) z (z + finiteEdgeStep 0) ω) =
          (fun n => limUnder atTop
            (fun m => C (right (hs n) m) z (z + finiteEdgeStep 0) ω)) :=
        funext fun n => (hRaw (hs n) z (z + finiteEdgeStep 0) ω).2
      have hh :
          Tendsto (fun n => Bm (hs n) z (z + finiteEdgeStep 0) ω) atTop
            (𝓝 (Bm q z (z + finiteEdgeStep 0) ω)) ∧
          Tendsto (fun n => Bp (hs n) z (z + finiteEdgeStep 0) ω) atTop
            (𝓝 (Bm q z (z + finiteEdgeStep 0) ω)) := by
        rw [hBmSeq, hBpSeq, (hRaw q z (z + finiteEdgeStep 0) ω).1]
        exact hc
      simpa using hh
    · have hc := (hNorthNegCont z).1 q hs hSide hLim
      have hBmSeq :
          (fun n => limUnder atTop
            (fun m => -(C (left (hs n) m) z (z + finiteEdgeStep 1) ω))) =
          (fun n => -(Bm (hs n) z (z + finiteEdgeStep 1) ω)) :=
        funext fun n => hNegBm (hs n) z
      have hBpSeq :
          (fun n => limUnder atTop
            (fun m => -(C (right (hs n) m) z (z + finiteEdgeStep 1) ω))) =
          (fun n => -(Bp (hs n) z (z + finiteEdgeStep 1) ω)) :=
        funext fun n => hNegBp (hs n) z
      rw [hBmSeq, hBpSeq, hNegBm q z] at hc
      have hh :
          Tendsto (fun n => Bm (hs n) z (z + finiteEdgeStep 1) ω) atTop
            (𝓝 (Bm q z (z + finiteEdgeStep 1) ω)) ∧
          Tendsto (fun n => Bp (hs n) z (z + finiteEdgeStep 1) ω) atTop
            (𝓝 (Bm q z (z + finiteEdgeStep 1) ω)) := by
        constructor
        · simpa only [neg_neg] using hc.1.neg
        · simpa only [neg_neg] using hc.2.neg
      simpa using hh
  have hEdgeRight (q : CoalescingTilt μ) (z : Lattice) (i : Fin 2)
      (hs : ℕ → CoalescingTilt μ)
      (hSide : ∀ n, q.val.1 < (hs n).val.1)
      (hLim : Tendsto hs atTop (𝓝 q)) :
      Tendsto (fun n => Bm (hs n) z (z + finiteEdgeStep i) ω) atTop
        (𝓝 (Bp q z (z + finiteEdgeStep i) ω)) ∧
      Tendsto (fun n => Bp (hs n) z (z + finiteEdgeStep i) ω) atTop
        (𝓝 (Bp q z (z + finiteEdgeStep i) ω)) := by
    fin_cases i
    · have hc := (hEastCont z).2 q hs hSide hLim
      have hBmSeq :
          (fun n => Bm (hs n) z (z + finiteEdgeStep 0) ω) =
          (fun n => limUnder atTop
            (fun m => C (left (hs n) m) z (z + finiteEdgeStep 0) ω)) :=
        funext fun n => (hRaw (hs n) z (z + finiteEdgeStep 0) ω).1
      have hBpSeq :
          (fun n => Bp (hs n) z (z + finiteEdgeStep 0) ω) =
          (fun n => limUnder atTop
            (fun m => C (right (hs n) m) z (z + finiteEdgeStep 0) ω)) :=
        funext fun n => (hRaw (hs n) z (z + finiteEdgeStep 0) ω).2
      have hh :
          Tendsto (fun n => Bm (hs n) z (z + finiteEdgeStep 0) ω) atTop
            (𝓝 (Bp q z (z + finiteEdgeStep 0) ω)) ∧
          Tendsto (fun n => Bp (hs n) z (z + finiteEdgeStep 0) ω) atTop
            (𝓝 (Bp q z (z + finiteEdgeStep 0) ω)) := by
        rw [hBmSeq, hBpSeq, (hRaw q z (z + finiteEdgeStep 0) ω).2]
        exact hc
      simpa using hh
    · have hc := (hNorthNegCont z).2 q hs hSide hLim
      have hBmSeq :
          (fun n => limUnder atTop
            (fun m => -(C (left (hs n) m) z (z + finiteEdgeStep 1) ω))) =
          (fun n => -(Bm (hs n) z (z + finiteEdgeStep 1) ω)) :=
        funext fun n => hNegBm (hs n) z
      have hBpSeq :
          (fun n => limUnder atTop
            (fun m => -(C (right (hs n) m) z (z + finiteEdgeStep 1) ω))) =
          (fun n => -(Bp (hs n) z (z + finiteEdgeStep 1) ω)) :=
        funext fun n => hNegBp (hs n) z
      rw [hBmSeq, hBpSeq, hNegBp q z] at hc
      have hh :
          Tendsto (fun n => Bm (hs n) z (z + finiteEdgeStep 1) ω) atTop
            (𝓝 (Bp q z (z + finiteEdgeStep 1) ω)) ∧
          Tendsto (fun n => Bp (hs n) z (z + finiteEdgeStep 1) ω) atTop
            (𝓝 (Bp q z (z + finiteEdgeStep 1) ω)) := by
        constructor
        · simpa only [neg_neg] using hc.1.neg
        · simpa only [neg_neg] using hc.2.neg
      simpa using hh

  have hPairBm (q : CoalescingTilt μ) (a b : Lattice) :
      Bm q a b ω =
        (if a.1 ≤ b.1 then
          ∑ k ∈ Finset.Ico a.1 b.1,
            Bm q (k, a.2) ((k, a.2) + finiteEdgeStep 0) ω
         else -(∑ k ∈ Finset.Ico b.1 a.1,
            Bm q (k, a.2) ((k, a.2) + finiteEdgeStep 0) ω)) +
        (if a.2 ≤ b.2 then
          ∑ k ∈ Finset.Ico a.2 b.2,
            Bm q (b.1, k) ((b.1, k) + finiteEdgeStep 1) ω
         else -(∑ k ∈ Finset.Ico b.2 a.2,
            Bm q (b.1, k) ((b.1, k) + finiteEdgeStep 1) ω)) := by
    have hLimit := signed_pair_tendsto_of_edges
      (fun n u v => C (left q n) u v ω)
      (fun u v => Bm q u v ω)
      (fun n u v => additive_eq_signed_edge_sums_global
        (fun s t => C (left q n) s t ω)
        (hAdd ⟨left q n, hLeftMem q n⟩) u v)
      (fun z i => (hEdgeFinite q z i).1) a b
    exact (hRaw q a b ω).1.trans hLimit.limUnder_eq
  have hPairBp (q : CoalescingTilt μ) (a b : Lattice) :
      Bp q a b ω =
        (if a.1 ≤ b.1 then
          ∑ k ∈ Finset.Ico a.1 b.1,
            Bp q (k, a.2) ((k, a.2) + finiteEdgeStep 0) ω
         else -(∑ k ∈ Finset.Ico b.1 a.1,
            Bp q (k, a.2) ((k, a.2) + finiteEdgeStep 0) ω)) +
        (if a.2 ≤ b.2 then
          ∑ k ∈ Finset.Ico a.2 b.2,
            Bp q (b.1, k) ((b.1, k) + finiteEdgeStep 1) ω
         else -(∑ k ∈ Finset.Ico b.2 a.2,
            Bp q (b.1, k) ((b.1, k) + finiteEdgeStep 1) ω)) := by
    have hLimit := signed_pair_tendsto_of_edges
      (fun n u v => C (right q n) u v ω)
      (fun u v => Bp q u v ω)
      (fun n u v => additive_eq_signed_edge_sums_global
        (fun s t => C (right q n) s t ω)
        (hAdd ⟨right q n, hRightMem q n⟩) u v)
      (fun z i => (hEdgeFinite q z i).2) a b
    exact (hRaw q a b ω).2.trans hLimit.limUnder_eq
  constructor
  · intro hs hSide hLim
    have hBmLimit := signed_pair_tendsto_of_edges
      (fun n a b => Bm (hs n) a b ω)
      (fun a b => Bm h a b ω)
      (fun n a b => hPairBm (hs n) a b)
      (fun z i => (hEdgeLeft h z i hs hSide hLim).1) x y
    have hBpLimit := signed_pair_tendsto_of_edges
      (fun n a b => Bp (hs n) a b ω)
      (fun a b => Bm h a b ω)
      (fun n a b => hPairBp (hs n) a b)
      (fun z i => (hEdgeLeft h z i hs hSide hLim).2) x y
    rw [← hPairBm h x y] at hBmLimit hBpLimit
    exact ⟨hBmLimit, hBpLimit⟩
  · intro hs hSide hLim
    have hBmLimit := signed_pair_tendsto_of_edges
      (fun n a b => Bm (hs n) a b ω)
      (fun a b => Bp h a b ω)
      (fun n a b => hPairBm (hs n) a b)
      (fun z i => (hEdgeRight h z i hs hSide hLim).1) x y
    have hBpLimit := signed_pair_tendsto_of_edges
      (fun n a b => Bp (hs n) a b ω)
      (fun a b => Bp h a b ω)
      (fun n a b => hPairBp (hs n) a b)
      (fun z i => (hEdgeRight h z i hs hSide hLim).2) x y
    rw [← hPairBp h x y] at hBmLimit hBpLimit
    exact ⟨hBmLimit, hBpLimit⟩

end LPP.Busemann
