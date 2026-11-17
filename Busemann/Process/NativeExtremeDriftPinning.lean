/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.NativeDriftMajorant
public import Busemann.Process.ExtremeDriftPinning
import LPP_Foundations.Analysis.AbsoluteMomentShape

/-! Apply native drift majorization to pin a canonical drift at an extreme support. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal NNReal BigOperators Topology

namespace LPP.Busemann

/-- At a fixed direction, an extreme supporting tilt pins the full-action
conditional drift to its two prescribed mean coordinates. This is the native
fixed-direction application of JR1810.03580v3, Lemma 4.5(b,c). -/
theorem ae_canonical_drift_pinned_at_extreme_support
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P)
    (hRec : recovers_weight_map_ae P processEnvironment B)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g)
    (η : InteriorDirection) (h : SupportTilt g)
    (hh : SupportsAt g η h.1)
    (hext : (∀ k : SupportTilt g, SupportsAt g η k.1 → h.1.1 ≤ k.1.1) ∨
      (∀ k : SupportTilt g, SupportsAt g η k.1 → k.1.1 ≤ h.1.1))
    (hMean : ∀ i : Fin 2,
      (∫ s, B 0 (finiteEdgeStep i) s ∂P) = -finiteTiltCoordinate h.1 i) :
    let mProc : MeasurableSpace ProcessSample := inferInstance
    let I : MeasurableSpace ProcessSample :=
      ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
    letI : MeasurableSpace ProcessSample := mProc
    let u : Fin 2 → ProcessSample → ℝ :=
      fun i => P[B 0 (finiteEdgeStep i) | I]
    ∀ᵐ s ∂P, SupportsAt g η (-u 0 s, -u 1 s) ∧
      ∀ i : Fin 2, u i s = -finiteTiltCoordinate h.1 i := by
  classical
  have hGeometry :=
    LPPDifferentiability.expected_rate_shape_geometry_of_absolute_moment
      μ g hmoment hg
  have hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z := by
    intro c z
    change g (c * z.1, c * z.2) = (c : ℝ) * g z
    exact hGeometry.2.1 c z

  let mProc : MeasurableSpace ProcessSample := inferInstance
  let I : MeasurableSpace ProcessSample :=
    ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
  let : MeasurableSpace ProcessSample := mProc
  let u : Fin 2 → ProcessSample → ℝ :=
    fun i => P[B 0 (finiteEdgeStep i) | I]

  -- Conditional expectation uses the original process measure and its full invariant algebra.
  have hI : I ≤ mProc :=
    (iInf_le (fun z : Lattice =>
      @MeasurableSpace.invariants ProcessSample mProc (processShift z)) (0 : Lattice)).trans
      (MeasurableSpace.invariants_le (processShift (0 : Lattice)))
  let : IsFiniteMeasure (P.trim hI) := inferInstance
  let : SigmaFinite (P.trim hI) := inferInstance
  have hUIntegrable : ∀ i : Fin 2, Integrable (u i) P := by
    intro i
    exact integrable_condExp
  have hUMean : ∀ i : Fin 2,
      (∫ s, u i s ∂P) = -finiteTiltCoordinate h.1 i := by
    intro i
    calc
      (∫ s, u i s ∂P) = ∫ s, B 0 (finiteEdgeStep i) s ∂P := by
        exact integral_condExp hI
      _ = -finiteTiltCoordinate h.1 i := hMean i

  -- The native producer supplies the same canonical drift's majorant.
  have hMajorant := ae_canonical_drift_majorizes_expected_shape
    μ hmoment P hMarginal hShift B hB hInt hRec g hg
  exact ae_drift_eq_of_extreme_support_mean g hhom P u hUIntegrable
    η h hh hext hUMean hMajorant

end LPP.Busemann
