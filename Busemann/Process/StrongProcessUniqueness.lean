/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.CanonicalCocycleUniqueness
public import Busemann.Geometry.CanonicalHSidedSequences
public import Busemann.Process.TiltIndexedBusemannProcess
public import LPP_Foundations.Statements.WeightMoments

import Busemann.Probability.CanonicalInvariantConditionalMean
import Busemann.Probability.CocycleMeanTilt

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

/-- Two tilt-indexed Busemann processes agree on one full-measure event at
every tilt and lattice pair in both branches. -/
theorem ae_eq_strong_busemann_process_of_six_properties
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : LPPStatements.HasAbsoluteMomentAbove μ 2)
    (Bm Bp Bm' Bp' : StrongField μ)
    (hFirst : IsTiltIndexedBusemannProcess μ Bm Bp)
    (hSecond : IsTiltIndexedBusemannProcess μ Bm' Bp') :
    ∀ᵐ ω ∂environmentLaw μ, ∀ (h : CoalescingTilt μ) (x y : Lattice),
      Bm' h x y ω = Bm h x y ω ∧ Bp' h x y ω = Bp h x y ω := by
  classical
  have hFirst := (is_tilt_indexed_busemann_process_iff μ Bm Bp).mp hFirst
  have hSecond := (is_tilt_indexed_busemann_process_iff μ Bm' Bp').mp hSecond
  let P : Measure Environment := environmentLaw μ
  let T : Lattice → Environment → Environment :=
    fun z ω => environmentTranslationEquiv z ω
  obtain ⟨D, hD, hSides⟩ :=
    exists_countable_sided_sample_coalescingTilts μ hμ hmoment
  obtain ⟨left, right, hSequences⟩ :=
    exists_canonical_H_sample_sided_sequences μ hμ hmoment D hSides
  have hFullTilt (X Y : StrongField μ)
      (hClass : ForwardCoalescingClass μ X Y)
      (hMean : MeanTilt μ X)
      (h : CoalescingTilt μ) :
      ∀ᵐ ω ∂P,
        invariantCocycleTilt P T (fun ω => ω)
          (X h) (hClass h).2.1 ω = h.val := by
    let mEnv : MeasurableSpace Environment := inferInstance
    let I : MeasurableSpace Environment :=
      @latticeInvariantSigma Environment mEnv T
    let : MeasurableSpace Environment := mEnv
    have he := canonical_condExp_full_invariants_eq_mean μ
      (X h 0 ((1 : ℤ), (0 : ℤ)))
      ((hClass h).2.1.2.2 0 ((1 : ℤ), (0 : ℤ)))
    have hn := canonical_condExp_full_invariants_eq_mean μ
      (X h 0 ((0 : ℤ), (1 : ℤ)))
      ((hClass h).2.1.2.2 0 ((0 : ℤ), (1 : ℤ)))
    have hTilt : meanCocycleTilt P (X h) = h.val :=
      (meanCocycleTilt_eq_iff P (X h) h.val).mpr (hMean h)
    filter_upwards [he, hn] with ω heω hnω
    calc
      invariantCocycleTilt P T (fun ω => ω) (X h) (hClass h).2.1 ω =
          meanCocycleTilt P (X h) := by
        change (-(P[X h 0 (1, 0) | I] ω), -(P[X h 0 (0, 1) | I] ω)) =
          meanCocycleTilt P (X h)
        exact Prod.ext (congrArg (fun v : ℝ => -v) heω) (congrArg (fun v : ℝ => -v) hnω)
      _ = h.val := hTilt
  have hAtD (d : CoalescingTilt μ) :
      ∀ᵐ ω ∂P, ∀ x y : Lattice,
        Bm' d x y ω = Bm d x y ω ∧
        Bp' d x y ω = Bp d x y ω := by
    have hMinus := ae_eq_of_coalescing_canonical_cocycles_same_tilt
      μ (Bm' d) (Bm d)
      (hSecond.2.1 d).2.1 (hFirst.2.1 d).2.1
      (hSecond.2.1 d).2.2.1 (hFirst.2.1 d).2.2.1
      d.val
      (hFullTilt Bm' Bp' hSecond.2.1 hSecond.2.2.1 d)
      (hFullTilt Bm Bp hFirst.2.1 hFirst.2.2.1 d)
    filter_upwards [hMinus, hFirst.1 d, hSecond.1 d] with ω hm hf hs
    intro x y
    exact ⟨hm x y, (hs x y).symm.trans ((hm x y).trans (hf x y))⟩
  have : Countable {d : CoalescingTilt μ // d ∈ D} := hD.to_subtype
  have hAtSample : ∀ᵐ ω ∂P,
      ∀ d : {d : CoalescingTilt μ // d ∈ D}, ∀ x y : Lattice,
        Bm' d.val x y ω = Bm d.val x y ω ∧
        Bp' d.val x y ω = Bp d.val x y ω := by
    apply ae_all_iff.mpr
    intro d
    exact hAtD d.val
  filter_upwards [hAtSample, hFirst.2.2.2.2.2, hSecond.2.2.2.2.2]
    with ω hSample hLimits hLimits'
  intro h x y
  by_cases hd : h ∈ D
  · exact hSample ⟨h, hd⟩ x y
  · rcases (hSequences h).2 hd with
      ⟨hLeft, _hLeftMono, hLeftLim, hRight, _hRightAnti, hRightLim⟩
    have hLeftEq :
        (fun n => Bm' (left h n) x y ω) =
          (fun n => Bm (left h n) x y ω) := by
      funext n
      exact (hSample ⟨left h n, (hLeft n).1⟩ x y).1
    have hRightEq :
        (fun n => Bp' (right h n) x y ω) =
          (fun n => Bp (right h n) x y ω) := by
      funext n
      exact (hSample ⟨right h n, (hRight n).1⟩ x y).2
    have hLeftFirst :=
      (hLimits h x y).1 (left h) (fun n => (hLeft n).2) hLeftLim
    have hLeftSecond :=
      (hLimits' h x y).1 (left h) (fun n => (hLeft n).2) hLeftLim
    have hRightFirst :=
      (hLimits h x y).2 (right h) (fun n => (hRight n).2) hRightLim
    have hRightSecond :=
      (hLimits' h x y).2 (right h) (fun n => (hRight n).2) hRightLim
    constructor
    · exact tendsto_nhds_unique (by simpa only [hLeftEq] using hLeftSecond.1)
        hLeftFirst.1
    · exact tendsto_nhds_unique (by simpa only [hRightEq] using hRightSecond.2)
        hRightFirst.2

end LPP.Busemann
