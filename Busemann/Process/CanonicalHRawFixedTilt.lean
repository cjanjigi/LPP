/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.CanonicalStrictCocycleOrder
public import Busemann.Process.CanonicalCocycleUniqueness
public import Busemann.Frozen.StrongExistence.Definitions.MeanTilt

import Busemann.Process.CanonicalHRawEnvelopes
import Busemann.Process.MonotoneCocycleLimit
import Busemann.Probability.CanonicalInvariantConditionalMean
import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

/-- At each fixed coalescing tilt, the two literal countable-sided limits
agree almost surely and have the required class and mean properties;
Strong Existence, public source Lemma extend=, lines 1212–1217. -/
theorem canonical_H_raw_fields_fixed_tilt_class_and_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (C : StrongField μ)
    (hClass : ForwardCoalescingClass μ C C)
    (hMean : MeanTilt μ C)
    (D : Set (CoalescingTilt μ))
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
    BranchAgreement μ Bm Bp ∧
      ForwardCoalescingClass μ Bm Bp ∧ MeanTilt μ Bm := by
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
        C b x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
          C a x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
        C a x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
          C b x (x + ((0 : ℤ), (1 : ℤ))) ω :=
    ae_forward_coalescing_cocycle_opposite_edge_order
      μ hμ hmoment (C a) (C b) (hGen a) (hGen b)
      (hForward a) (hForward b) (hCoal a) (hCoal b)
      a.val b.val (hTilt a) (hTilt b) hab
  have hLimit (h : CoalescingTilt μ) (F : ℕ → CoalescingTilt μ)
      (hFlim : Tendsto F atTop (𝓝 h))
      (hForder :
        (∀ᵐ ω ∂P, ∀ n x,
          C (F (n + 1)) x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
            C (F n) x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
          C (F n) x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
            C (F (n + 1)) x (x + ((0 : ℤ), (1 : ℤ))) ω) ∨
        (∀ᵐ ω ∂P, ∀ n x,
          C (F n) x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
            C (F (n + 1)) x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
          C (F (n + 1)) x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
            C (F n) x (x + ((0 : ℤ), (1 : ℤ))) ω)) :
      ∀ᵐ ω ∂P, ∀ x y : Lattice,
        Tendsto (fun n => C (F n) x y ω) atTop (𝓝 (C h x y ω)) := by
    have hPair : Tendsto (fun n => (F n).val) atTop (𝓝 h.val) :=
      continuous_subtype_val.tendsto h |>.comp hFlim
    obtain ⟨L, hL, hLf, hLc, hLt, hLlim, _, _, _⟩ :=
      exists_forward_coalescing_monotone_cocycle_limit
        μ hμ hmoment (fun n => C (F n)) (fun n => hGen (F n))
        (fun n => hForward (F n)) (fun n => (F n).val) h.val
        (fun n => hTilt (F n)) hPair hForder
    have hEq := ae_eq_of_coalescing_canonical_cocycles_same_tilt
      μ L (C h) hL (hGen h) hLc (hCoal h) h.val hLt (hTilt h)
    filter_upwards [hLlim, hEq] with ω hlim heq
    intro x y
    simpa only [heq x y] using hlim x y
  have hRawEq (h : CoalescingTilt μ) :
      ∀ᵐ ω ∂P, ∀ x y : Lattice,
        Bm h x y ω = C h x y ω ∧ Bp h x y ω = C h x y ω := by
    by_cases hd : h ∈ D
    · have hc := (hSequences h).1 hd
      exact Filter.Eventually.of_forall (fun ω x y => by
        constructor
        · rw [(hRaw h x y ω).1, hc.1]
          exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => C h x y ω)
            atTop (𝓝 (C h x y ω))).limUnder_eq
        · rw [(hRaw h x y ω).2, hc.2]
          exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => C h x y ω)
            atTop (𝓝 (C h x y ω))).limUnder_eq)
    · rcases (hSequences h).2 hd with
        ⟨hLeft, hLeftMono, hLeftLim, hRight, hRightAnti, hRightLim⟩
      have hlOrder :
          (∀ᵐ ω ∂P, ∀ n x,
            C (left h (n + 1)) x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
              C (left h n) x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
            C (left h n) x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
              C (left h (n + 1)) x (x + ((0 : ℤ), (1 : ℤ))) ω) ∨
          (∀ᵐ ω ∂P, ∀ n x,
            C (left h n) x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
              C (left h (n + 1)) x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
            C (left h (n + 1)) x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
              C (left h n) x (x + ((0 : ℤ), (1 : ℤ))) ω) := by
        left
        apply ae_all_iff.mpr
        intro n
        exact hStrict (left h n) (left h (n + 1))
          (hLeftMono n.lt_succ_self)
      have hrOrder :
          (∀ᵐ ω ∂P, ∀ n x,
            C (right h (n + 1)) x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
              C (right h n) x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
            C (right h n) x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
              C (right h (n + 1)) x (x + ((0 : ℤ), (1 : ℤ))) ω) ∨
          (∀ᵐ ω ∂P, ∀ n x,
            C (right h n) x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
              C (right h (n + 1)) x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
            C (right h (n + 1)) x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
              C (right h n) x (x + ((0 : ℤ), (1 : ℤ))) ω) := by
        right
        apply ae_all_iff.mpr
        intro n
        exact hStrict (right h (n + 1)) (right h n)
          (hRightAnti n.lt_succ_self)
      have hl := hLimit h (left h) hLeftLim hlOrder
      have hr := hLimit h (right h) hRightLim hrOrder
      filter_upwards [hl, hr] with ω hlω hrω
      intro x y
      exact ⟨(hRaw h x y ω).1.trans (hlω x y).limUnder_eq,
        (hRaw h x y ω).2.trans (hrω x y).limUnder_eq⟩
  have hForwardBm (h : CoalescingTilt μ) : IsForwardMeasurable (Bm h) := by
    have heq : Bm h =
        (fun x y ω => limUnder atTop (fun n => C (left h n) x y ω)) := by
      funext x y ω
      exact (hRaw h x y ω).1
    rw [heq]
    exact isForwardMeasurable_limUnder
      (fun n x y ω => C (left h n) x y ω)
      (fun n => hForward (left h n))
  have hMeasBp (h : CoalescingTilt μ) :
      Measurable (fun q : (Lattice × Lattice) × Environment =>
        Bp h q.1.1 q.1.2 q.2) := by
    have heq : (fun q : (Lattice × Lattice) × Environment =>
        Bp h q.1.1 q.1.2 q.2) =
        (fun q : (Lattice × Lattice) × Environment =>
          limUnder atTop (fun n => C (right h n) q.1.1 q.1.2 q.2)) := by
      funext q
      exact (hRaw h q.1.1 q.1.2 q.2).2
    rw [heq]
    exact (StronglyMeasurable.limUnder
      (fun n => ((hGen (right h n)).1.1).stronglyMeasurable)).measurable
  have hGenBm (h : CoalescingTilt μ) :
      IsGeneralizedBusemann P T (fun ω => ω) (Bm h) := by
    have heq : ∀ᵐ ω ∂P, ∀ x y : Lattice,
        Bm h x y ω = C h x y ω := by
      filter_upwards [hRawEq h] with ω hw
      exact fun x y => (hw x y).1
    have hMeas : Measurable (fun q : (Lattice × Lattice) × Environment =>
        Bm h q.1.1 q.1.2 q.2) := by
      have heq : (fun q : (Lattice × Lattice) × Environment =>
          Bm h q.1.1 q.1.2 q.2) =
          (fun q : (Lattice × Lattice) × Environment =>
            limUnder atTop (fun n => C (left h n) q.1.1 q.1.2 q.2)) := by
        funext q
        exact (hRaw h q.1.1 q.1.2 q.2).1
      rw [heq]
      exact (StronglyMeasurable.limUnder
        (fun n => ((hGen (left h n)).1.1).stronglyMeasurable)).measurable
    have hCov (x y z : Lattice) : ∀ᵐ ω ∂P,
        Bm h (x + z) (y + z) ω = Bm h x y (T z ω) := by
      have hShifted := (measurePreserving_environmentTranslationEquiv μ z)
        |>.quasiMeasurePreserving.ae heq
      filter_upwards [heq, hShifted, (hGen h).1.2.1 x y z] with ω hw hs hc
      rw [hw (x + z) (y + z), hc, hs x y]
    have hAdd : ∀ᵐ ω ∂P,
        is_additive (fun x y => Bm h x y ω) := by
      filter_upwards [heq, (hGen h).1.2.2] with ω hw ha
      intro x y z
      change Bm h x y ω + Bm h y z ω = Bm h x z ω
      rw [hw x y, hw y z, hw x z]
      exact ha x y z
    have hRec : recovers_weight_map_ae P (fun ω => ω) (Bm h) := by
      filter_upwards [heq, (hGen h).2.1] with ω hw hr
      intro x
      change min (Bm h x (x + (1, 0)) ω) (Bm h x (x + (0, 1)) ω) = ω x
      rw [hw x (x + (1, 0)), hw x (x + (0, 1))]
      exact hr x
    have hInt (x y : Lattice) : Integrable (Bm h x y) P := by
      have hEq : Bm h x y =ᵐ[P] C h x y := by
        filter_upwards [heq] with ω hw
        exact hw x y
      exact ((hGen h).2.2 x y).congr hEq.symm
    exact ⟨⟨hMeas, hCov, hAdd⟩, hRec, hInt⟩
  have hCoalBm (h : CoalescingTilt μ) :
      HasCoalescingRightmostPaths P (Bm h) := by
    filter_upwards [hRawEq h, hCoal h] with ω heq hco
    have hFields : (fun x y => Bm h x y ω) = (fun x y => C h x y ω) := by
      funext x y
      exact (heq x y).1
    simpa only [hFields] using hco
  have hMeanBm (h : CoalescingTilt μ) :
      (∫ ω, Bm h 0 (1, 0) ω ∂P) = -h.val.1 ∧
      (∫ ω, Bm h 0 (0, 1) ω ∂P) = -h.val.2 := by
    have he : Bm h 0 (1, 0) =ᵐ[P] C h 0 (1, 0) := by
      filter_upwards [hRawEq h] with ω hw
      exact (hw 0 (1, 0)).1
    have hn : Bm h 0 (0, 1) =ᵐ[P] C h 0 (0, 1) := by
      filter_upwards [hRawEq h] with ω hw
      exact (hw 0 (0, 1)).1
    exact ⟨(integral_congr_ae he).trans (hMean h).1,
      (integral_congr_ae hn).trans (hMean h).2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    filter_upwards [hRawEq h] with ω hw
    intro x y
    exact (hw x y).1.trans (hw x y).2.symm
  · intro h
    exact ⟨hMeasBp h, hGenBm h, hCoalBm h, hForwardBm h⟩
  · exact hMeanBm

end LPP.Busemann
