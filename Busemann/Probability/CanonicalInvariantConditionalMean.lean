/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.LatticeInvariantSigma
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Probability.TranslationEquiv
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import LPP_Foundations.Probability.TranslationErgodic
import Mathlib.Dynamics.Ergodic.Function

@[expose] public section
open MeasureTheory LPPDifferentiability
namespace LPP.Busemann

-- The named parameter `hf` is part of the shared theorem interface.
set_option linter.unusedVariables false in
/-- The full lattice-invariant conditional mean is the ordinary mean under
the canonical iid environment law. -/
theorem canonical_condExp_full_invariants_eq_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : LPPDifferentiability.Environment → ℝ)
    (hf : Integrable f (environmentLaw μ)) :
    (environmentLaw μ)[f | latticeInvariantSigma
      (fun z ω => environmentTranslationEquiv z ω)] =ᵐ[environmentLaw μ]
      (fun _ => ∫ ω, f ω ∂environmentLaw μ) := by
  let mEnv : MeasurableSpace Environment := inferInstance
  let T : Lattice → Environment → Environment :=
    fun z ω => environmentTranslationEquiv z ω
  let I : MeasurableSpace Environment := @latticeInvariantSigma Environment mEnv T
  let : MeasurableSpace Environment := mEnv
  let P : Measure Environment := environmentLaw μ
  change P[f | I] =ᵐ[P] (fun _ => ∫ ω, f ω ∂P)
  have hIle : I ≤ mEnv := by
    change (⨅ z : Lattice, @MeasurableSpace.invariants Environment mEnv (T z)) ≤ mEnv
    exact (iInf_le _ (0 : Lattice)).trans (MeasurableSpace.invariants_le (T 0))
  let : SigmaFinite (P.trim hIle) := inferInstance
  have hEast : I ≤ MeasurableSpace.invariants (T (1, 0)) := by
    change (⨅ z : Lattice, @MeasurableSpace.invariants Environment mEnv (T z)) ≤
      MeasurableSpace.invariants (T (1, 0))
    exact iInf_le _ (1, 0)
  have hMeasI : Measurable[I] (P[f | I]) := stronglyMeasurable_condExp.measurable
  have hMeasEast : Measurable[MeasurableSpace.invariants (T (1, 0))]
      (P[f | I]) := hMeasI.mono hEast le_rfl
  have hInvariant : (P[f | I]) ∘ T (1, 0) = P[f | I] :=
    MeasurableSpace.comp_eq_of_measurable_invariants hMeasEast
  have hMeas : Measurable (P[f | I]) :=
    hMeasEast.mono (MeasurableSpace.invariants_le (T (1, 0))) le_rfl
  have hErgodic : Ergodic (T (1, 0)) P :=
    ergodic_environment_translation μ (1, 0) (by decide)
  obtain ⟨c, hc⟩ := hErgodic.ae_eq_const_of_ae_eq_comp₀ hMeas.nullMeasurable
    (Filter.Eventually.of_forall fun ω => congrFun hInvariant ω)
  have hMean : c = ∫ ω, f ω ∂P := by
    have hIntegral : (∫ ω, P[f | I] ω ∂P) = c := by
      rw [integral_congr_ae hc]
      simp
    calc
      c = ∫ ω, P[f | I] ω ∂P := hIntegral.symm
      _ = ∫ ω, f ω ∂P := integral_condExp hIle
  filter_upwards [hc] with ω hω
  change P[f | I] ω = c at hω
  exact hω.trans hMean

end LPP.Busemann
