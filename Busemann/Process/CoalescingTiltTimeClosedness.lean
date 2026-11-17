/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.TimeSet
public import Martin2004.Statements.ShapeFacts
public import Mathlib.Topology.Sequences

import Busemann.Process.CoalescingTiltTimeConvergence
import Busemann.Process.CoalescingTiltSupport
import Busemann.Process.CanonicalForwardCocycleVersion
import Busemann.Process.CanonicalStrictCocycleOrder
import Busemann.Process.MonotoneCocycleLimit
import Busemann.Frozen.Variational.OneSidedBound
import Busemann.Geometry.SupportOrder
import LPP_Foundations.Analysis.AbsoluteMomentShape
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic.Linarith

/-! Closedness of the canonical coalescing tilt time set. The closedness
assembly is the author's unpublished argument; its source ingredients are
handled by the imported support, comparison, and monotone-limit theorems. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal NNReal Topology

namespace LPP.Busemann

/-- Under the original iid law assumptions, the time coordinates of canonical
coalescing tilts form a closed subset of the real line. -/
theorem isClosed_timeSet_of_absolute_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    IsClosed (timeSet μ) := by
  classical
  apply IsSeqClosed.isClosed
  intro times t hTimes hTimesLimit
  have hTimesWitness (n : ℕ) : ∃ s : CoalescingTilt μ,
      times n = s.val.1 - s.val.2 := hTimes n
  choose tilts hTimeAt using hTimesWitness
  have hScalarLimit :
      Tendsto (fun n => (tilts n).val.1 - (tilts n).val.2) atTop (𝓝 t) := by
    convert hTimesLimit using 1
    funext n
    exact (hTimeAt n).symm
  obtain ⟨φ, _hφ, h, hPairLimit, ht⟩ :=
    exists_coalescing_tilt_subseq_of_time_tendsto
      μ hμ hmoment tilts t hScalarLimit

  -- The library's infinite Erdős–Szekeres theorem gives both orientations.
  obtain ⟨gIndex, hDirection⟩ :=
    exists_increasing_or_nonincreasing_subseq (fun a b : ℝ => a < b)
      (fun n => (tilts (φ n)).val.1)
  let σ : ℕ → ℕ := fun n => φ (gIndex n)
  let s : ℕ → CoalescingTilt μ := fun n => tilts (σ n)
  have hTiltLimit : Tendsto (fun n => (s n).val) atTop (𝓝 h) := by
    exact hPairLimit.comp gIndex.strictMono.tendsto_atTop
  have hFirstOrder :
      Monotone (fun n => (s n).val.1) ∨
        Antitone (fun n => (s n).val.1) := by
    rcases hDirection with hInc | hNoninc
    · left
      intro a b hab
      by_cases heq : a = b
      · subst b; exact le_refl _
      · have hlt : a < b := lt_of_le_of_ne hab heq
        exact le_of_lt (hInc a b hlt)
    · right
      intro a b hab
      by_cases heq : a = b
      · subst b; exact le_refl _
      · have hlt : a < b := lt_of_le_of_ne hab heq
        exact le_of_not_gt (hNoninc a b hlt)

  -- One common expected-rate shape identifies repeated first coordinates.
  obtain ⟨shape, hShape, _⟩ :=
    exists_expected_rate_shape_le_cocycle_essSup μ hmoment
  have hGeometry :=
    expected_rate_shape_geometry_of_absolute_moment μ shape hmoment hShape
  have hHomogeneous : ∀ (c : ℝ≥0) (z : Quadrant),
      shape (c • z) = (c : ℝ) * shape z := by
    intro c z
    change shape (c * z.1, c * z.2) = (c : ℝ) * shape z
    exact hGeometry.2.1 c z
  let support (a : CoalescingTilt μ) : SupportTilt shape :=
    Classical.choose (coalescingTilt_to_supportTilt μ hμ hmoment shape hShape a)
  have hSupportValue (a : CoalescingTilt μ) : (support a).val = a.val :=
    Classical.choose_spec
      (coalescingTilt_to_supportTilt μ hμ hmoment shape hShape a)
  have hSameTilt (a b : CoalescingTilt μ)
      (hFirst : a.val.1 = b.val.1) : a = b := by
    have hSupportFirst : (support a).val.1 = (support b).val.1 := by
      simpa only [hSupportValue] using hFirst
    have hSupportEq : support a = support b :=
      (supportTilt_coordinate_order shape hHomogeneous (support a) (support b)).2
        hSupportFirst
    apply Subtype.ext
    calc
      a.val = (support a).val := (hSupportValue a).symm
      _ = (support b).val := congrArg Subtype.val hSupportEq
      _ = b.val := hSupportValue b

  -- Choose one forward representative for each H subtype value. The common
  -- all-pair equality transfers both conditional edge expectations.
  have hVersion (a : CoalescingTilt μ) :
      ∃ V : Lattice → Lattice → Environment → ℝ,
        ∃ hV : IsGeneralizedBusemann (environmentLaw μ)
          (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) V,
          HasCoalescingRightmostPaths (environmentLaw μ) V ∧
          IsForwardMeasurable V ∧
          (∀ᵐ ω ∂environmentLaw μ,
            invariantCocycleTilt (environmentLaw μ)
              (fun z ω => environmentTranslationEquiv z ω)
              (fun ω => ω) V hV ω = a.val) := by
    obtain ⟨B, hB, hCoalB, hTiltB⟩ := a.property
    obtain ⟨V, hV, hCoalV, hForwardV, hVersionAE⟩ :=
      exists_forward_version_of_coalescing_canonical_cocycle
        μ hμ hmoment B hB hCoalB
    let P : Measure Environment := environmentLaw μ
    let T : Lattice → Environment → Environment :=
      fun z ω => environmentTranslationEquiv z ω
    let mEnv : MeasurableSpace Environment := inferInstance
    let I : MeasurableSpace Environment :=
      @latticeInvariantSigma Environment mEnv T
    let : MeasurableSpace Environment := mEnv
    have hEastAE :
        (fun ω => V 0 ((1 : ℤ), (0 : ℤ)) ω) =ᵐ[P]
          (fun ω => B 0 ((1 : ℤ), (0 : ℤ)) ω) := by
      filter_upwards [hVersionAE] with ω hω
      exact hω 0 ((1 : ℤ), (0 : ℤ))
    have hNorthAE :
        (fun ω => V 0 ((0 : ℤ), (1 : ℤ)) ω) =ᵐ[P]
          (fun ω => B 0 ((0 : ℤ), (1 : ℤ)) ω) := by
      filter_upwards [hVersionAE] with ω hω
      exact hω 0 ((0 : ℤ), (1 : ℤ))
    have hEastCond :
        P[V 0 ((1 : ℤ), (0 : ℤ)) | I] =ᵐ[P]
          P[B 0 ((1 : ℤ), (0 : ℤ)) | I] :=
      condExp_congr_ae hEastAE
    have hNorthCond :
        P[V 0 ((0 : ℤ), (1 : ℤ)) | I] =ᵐ[P]
          P[B 0 ((0 : ℤ), (1 : ℤ)) | I] :=
      condExp_congr_ae hNorthAE
    have hTiltV : ∀ᵐ ω ∂P,
        invariantCocycleTilt P T (fun ω => ω) V hV ω = a.val := by
      filter_upwards [hEastCond, hNorthCond, hTiltB] with ω hEast hNorth hTilt
      apply Prod.ext
      · change -(P[V 0 ((1 : ℤ), (0 : ℤ)) | I] ω) = a.val.1
        have hTiltEast := congrArg Prod.fst hTilt
        change -(P[B 0 ((1 : ℤ), (0 : ℤ)) | I] ω) = a.val.1 at hTiltEast
        rw [hEast]
        exact hTiltEast
      · change -(P[V 0 ((0 : ℤ), (1 : ℤ)) | I] ω) = a.val.2
        have hTiltNorth := congrArg Prod.snd hTilt
        change -(P[B 0 ((0 : ℤ), (1 : ℤ)) | I] ω) = a.val.2 at hTiltNorth
        rw [hNorth]
        exact hTiltNorth
    exact ⟨V, hV, hCoalV, hForwardV, hTiltV⟩
  choose V hV hRest using hVersion
  have hCoalV (a : CoalescingTilt μ) :
      HasCoalescingRightmostPaths (environmentLaw μ) (V a) := (hRest a).1
  have hForwardV (a : CoalescingTilt μ) : IsForwardMeasurable (V a) :=
    (hRest a).2.1
  have hTiltV (a : CoalescingTilt μ) : ∀ᵐ ω ∂environmentLaw μ,
      invariantCocycleTilt (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω)
        (V a) (hV a) ω = a.val := (hRest a).2.2
  let fields : ℕ → Lattice → Lattice → Environment → ℝ := fun n => V (s n)
  let pairs : ℕ → ℝ × ℝ := fun n => (s n).val
  have hFields (n : ℕ) : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) (fields n) :=
    hV (s n)
  have hForwards (n : ℕ) : IsForwardMeasurable (fields n) := hForwardV (s n)
  have hCoalesces (n : ℕ) : HasCoalescingRightmostPaths
      (environmentLaw μ) (fields n) := hCoalV (s n)
  have hTilts (n : ℕ) : ∀ᵐ ω ∂environmentLaw μ,
      invariantCocycleTilt (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω)
        (fields n) (hFields n) ω = pairs n := by
    exact hTiltV (s n)

  -- An equal adjacent tilt uses the same selected field. Unequal adjacent
  -- tilts use the strict comparison in the correct orientation.
  have hAdjacentIncreasing (hMono : Monotone (fun n => (s n).val.1))
      (n : ℕ) : ∀ᵐ ω ∂environmentLaw μ, ∀ x : Lattice,
      fields (n + 1) x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
        fields n x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
      fields n x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
        fields (n + 1) x (x + ((0 : ℤ), (1 : ℤ))) ω := by
    have hle := hMono (Nat.le_succ n)
    by_cases heq : (s n).val.1 = (s (n + 1)).val.1
    · have hsEq : s n = s (n + 1) := hSameTilt _ _ heq
      have hFieldEq : fields n = fields (n + 1) := congrArg V hsEq
      exact Filter.Eventually.of_forall fun ω x => by
        rw [hFieldEq]
        exact ⟨le_refl _, le_refl _⟩
    · have hlt : (pairs n).1 < (pairs (n + 1)).1 :=
        lt_of_le_of_ne hle heq
      exact ae_forward_coalescing_cocycle_opposite_edge_order
        μ hμ hmoment (fields n) (fields (n + 1))
        (hFields n) (hFields (n + 1))
        (hForwards n) (hForwards (n + 1))
        (hCoalesces n) (hCoalesces (n + 1))
        (pairs n) (pairs (n + 1)) (hTilts n) (hTilts (n + 1)) hlt
  have hAdjacentDecreasing (hAnti : Antitone (fun n => (s n).val.1))
      (n : ℕ) : ∀ᵐ ω ∂environmentLaw μ, ∀ x : Lattice,
      fields n x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
        fields (n + 1) x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
      fields (n + 1) x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
        fields n x (x + ((0 : ℤ), (1 : ℤ))) ω := by
    have hle := hAnti (Nat.le_succ n)
    by_cases heq : (s (n + 1)).val.1 = (s n).val.1
    · have hsEq : s (n + 1) = s n := hSameTilt _ _ heq
      have hFieldEq : fields (n + 1) = fields n := congrArg V hsEq
      exact Filter.Eventually.of_forall fun ω x => by
        rw [hFieldEq]
        exact ⟨le_refl _, le_refl _⟩
    · have hlt : (pairs (n + 1)).1 < (pairs n).1 :=
        lt_of_le_of_ne hle heq
      exact ae_forward_coalescing_cocycle_opposite_edge_order
        μ hμ hmoment (fields (n + 1)) (fields n)
        (hFields (n + 1)) (hFields n)
        (hForwards (n + 1)) (hForwards n)
        (hCoalesces (n + 1)) (hCoalesces n)
        (pairs (n + 1)) (pairs n) (hTilts (n + 1)) (hTilts n) hlt
  have hOrder :
      (∀ᵐ ω ∂environmentLaw μ, ∀ (n : ℕ) (x : Lattice),
        fields (n + 1) x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
          fields n x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
        fields n x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
          fields (n + 1) x (x + ((0 : ℤ), (1 : ℤ))) ω) ∨
      (∀ᵐ ω ∂environmentLaw μ, ∀ (n : ℕ) (x : Lattice),
        fields n x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
          fields (n + 1) x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
        fields (n + 1) x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
          fields n x (x + ((0 : ℤ), (1 : ℤ))) ω) := by
    rcases hFirstOrder with hMono | hAnti
    · exact Or.inl (ae_all_iff.mpr (hAdjacentIncreasing hMono))
    · exact Or.inr (ae_all_iff.mpr (hAdjacentDecreasing hAnti))

  obtain ⟨limitField, hLimitField, _hLimitForward, hLimitCoal,
      hLimitTilt, _hAlmostSure, _hLone, _hMeanEast, _hMeanNorth⟩ :=
    exists_forward_coalescing_monotone_cocycle_limit
      μ hμ hmoment fields hFields hForwards pairs h hTilts
      hTiltLimit hOrder
  have hInH : h ∈ coalescingTilts μ :=
    ⟨limitField, hLimitField, hLimitCoal, hLimitTilt⟩
  exact ⟨⟨h, hInH⟩, ht⟩

end LPP.Busemann
