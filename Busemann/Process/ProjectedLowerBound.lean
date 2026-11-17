/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.ProcessEnvironment
public import LPP_Foundations.Probability.EnvironmentLaw
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import LPP_Foundations.Probability.PassageIntegrable
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Lower bounds after environment projection

A conditional expectation given the environment preserves a lower bound by an
integrable site weight. This is the scalar projection step in JR
arXiv:1810.03580v3, proof of Theorem 4.8 after (4.20)-(4.21).
-/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- A measurable environment representative of a conditional expectation
dominates any integrable site-weight lower bound. See JR arXiv:1810.03580v3,
proof of Theorem 4.8 after equations (4.20)-(4.21). -/
theorem ae_environment_eval_le_of_condExp
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (x : Lattice)
    (f : ProcessSample → ℝ) (hf : Integrable f P)
    (hlower : ∀ᵐ s ∂P, (processEnvironment s) x ≤ f s)
    (b : Environment → ℝ) (hb : Measurable b)
    (hrep : ∀ᵐ s ∂P,
      b (processEnvironment s) =
        P[f | MeasurableSpace.comap processEnvironment
          (inferInstance : MeasurableSpace Environment)] s) :
    ∀ᵐ ω ∂environmentLaw μ, ω x ≤ b ω := by
  classical

  -- Keep the process sigma algebra fixed while naming the environment comap.
  let mProc : MeasurableSpace ProcessSample := inferInstance
  let mEnv := MeasurableSpace.comap processEnvironment
    (inferInstance : MeasurableSpace Environment)
  let : MeasurableSpace ProcessSample := mProc
  have hProjection : Measurable processEnvironment := measurable_fst
  have hm : mEnv ≤ mProc := hProjection.comap_le
  let : SigmaFinite (P.trim hm) := inferInstance

  -- The one-site first moment gives integrability under the canonical law.
  have hWeightEnvironment :
      Integrable (fun ω : Environment => ω x) (environmentLaw μ) :=
    integrable_environment_eval μ hμ x
  have hWeightMap :
      Integrable (fun ω : Environment => ω x) (P.map processEnvironment) := by
    rw [hMarginal]
    exact hWeightEnvironment
  have hWeight :
      Integrable (fun s : ProcessSample => (processEnvironment s) x) P := by
    change Integrable ((fun ω : Environment => ω x) ∘ processEnvironment) P
    exact (integrable_map_measure hWeightMap.aestronglyMeasurable
      hProjection.aemeasurable).mp hWeightMap

  -- The site coordinate is measurable for the actual environment comap.
  have hWeightMeasurable :
      Measurable[mEnv] (fun s : ProcessSample => (processEnvironment s) x) :=
    (measurable_pi_apply x).comp (comap_measurable processEnvironment)
  have hWeightStrong :
      StronglyMeasurable[mEnv] (fun s : ProcessSample => (processEnvironment s) x) :=
    hWeightMeasurable.stronglyMeasurable

  -- Conditioning leaves an integrable comap-measurable coordinate unchanged.
  have hWeightConditional :
      P[(fun s : ProcessSample => (processEnvironment s) x) | mEnv] =
        (fun s : ProcessSample => (processEnvironment s) x) :=
    condExp_of_stronglyMeasurable hm hWeightStrong hWeight

  -- Conditional expectation preserves the given almost-everywhere lower bound.
  have hConditionalLower :
      P[(fun s : ProcessSample => (processEnvironment s) x) | mEnv] ≤ᵐ[P]
        P[f | mEnv] :=
    condExp_mono hWeight hf hlower
  have hRepresentative :
      ∀ᵐ s ∂P, b (processEnvironment s) = P[f | mEnv] s := hrep
  have hProcessLower :
      ∀ᵐ s ∂P, (processEnvironment s) x ≤ b (processEnvironment s) := by
    filter_upwards [hConditionalLower, hRepresentative] with s hle hrep
    calc
      (processEnvironment s) x =
          P[(fun t : ProcessSample => (processEnvironment t) x) | mEnv] s := by
            rw [hWeightConditional]
      _ ≤ P[f | mEnv] s := hle
      _ = b (processEnvironment s) := hrep.symm

  -- The genuine process marginal transfers the bound to canonical environments.
  have hBoundSet : MeasurableSet {ω : Environment | ω x ≤ b ω} :=
    measurableSet_le (measurable_pi_apply x) hb
  rw [← hMarginal]
  rw [ae_map_iff hProjection.aemeasurable hBoundSet]
  exact hProcessLower

end LPP.Busemann
