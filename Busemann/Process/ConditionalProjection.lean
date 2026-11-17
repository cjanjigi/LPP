/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.ProcessEnvironment
public import LPP_Foundations.Probability.EnvironmentLaw
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! A scalar conditional expectation represented on the canonical environment. -/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

-- The named parameter `hf` is part of the shared theorem interface.
set_option linter.unusedVariables false in
/-- Conditioning an integrable coupled scalar on the environment has an
integrable canonical representative with the same mean, unique up to the
canonical law. This is the scalar projection step in JR arXiv:1810.03580v3,
proof of Theorem 4.8 after (4.20). -/
theorem exists_canonical_condExp_representative
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (f : ProcessSample → ℝ) (hf : Integrable f P) :
    let mEnv := MeasurableSpace.comap processEnvironment
      (inferInstance : MeasurableSpace Environment)
    ∃ b : Environment → ℝ,
      Measurable b ∧
      (∀ᵐ s ∂P, b (processEnvironment s) = P[f | mEnv] s) ∧
      Integrable b (environmentLaw μ) ∧
      (∫ ω, b ω ∂environmentLaw μ) = ∫ s, f s ∂P ∧
      ∀ b' : Environment → ℝ, Measurable b' →
        (∀ᵐ s ∂P, b' (processEnvironment s) = P[f | mEnv] s) →
        b' =ᵐ[environmentLaw μ] b := by
  let mProc : MeasurableSpace ProcessSample := inferInstance
  let mEnv := MeasurableSpace.comap processEnvironment
    (inferInstance : MeasurableSpace Environment)
  let : MeasurableSpace ProcessSample := mProc
  change ∃ b : Environment → ℝ,
      Measurable b ∧
      (∀ᵐ s ∂P, b (processEnvironment s) = P[f | mEnv] s) ∧
      Integrable b (environmentLaw μ) ∧
      (∫ ω, b ω ∂environmentLaw μ) = ∫ s, f s ∂P ∧
      ∀ b' : Environment → ℝ, Measurable b' →
        (∀ᵐ s ∂P, b' (processEnvironment s) = P[f | mEnv] s) →
        b' =ᵐ[environmentLaw μ] b
  -- The conditioning algebra is the projection comap, below the ambient product algebra.
  have hπ : Measurable processEnvironment := measurable_fst
  have hm : mEnv ≤ mProc := hπ.comap_le
  let : SigmaFinite (P.trim hm) := inferInstance
  -- The actual conditional-expectation representative factors through the projection.
  have hcond : StronglyMeasurable[mEnv] (P[f | mEnv]) := stronglyMeasurable_condExp
  obtain ⟨b, hbStrong, hbEq⟩ := hcond.exists_eq_measurable_comp
  have hb : Measurable b := hbStrong.measurable
  have hrep : ∀ᵐ s ∂P, b (processEnvironment s) = P[f | mEnv] s :=
    Filter.Eventually.of_forall fun s => (congrFun hbEq s).symm
  -- The actual marginal identifies the canonical integrability and integral.
  have hcomp : Integrable (b ∘ processEnvironment) P :=
    integrable_condExp.congr (Filter.Eventually.of_forall fun s => congrFun hbEq s)
  have hbMap : Integrable b (P.map processEnvironment) :=
    (integrable_map_measure hb.aestronglyMeasurable hπ.aemeasurable).2 hcomp
  have hbInt : Integrable b (environmentLaw μ) := by
    rw [← hMarginal]
    exact hbMap
  have hbMean : (∫ ω, b ω ∂environmentLaw μ) = ∫ s, f s ∂P := by
    calc
      (∫ ω, b ω ∂environmentLaw μ) = ∫ s, b (processEnvironment s) ∂P := by
        rw [← hMarginal]
        exact integral_map hπ.aemeasurable hb.aestronglyMeasurable
      _ = ∫ s, P[f | mEnv] s ∂P := integral_congr_ae hrep
      _ = ∫ s, f s ∂P := integral_condExp hm
  refine ⟨b, hb, hrep, hbInt, hbMean, ?_⟩
  -- Measurable versions agree under the canonical marginal, not pointwise.
  intro b' hb' hrep'
  rw [← hMarginal]
  change ∀ᵐ ω ∂P.map processEnvironment, b' ω = b ω
  rw [ae_map_iff hπ.aemeasurable (measurableSet_eq_fun hb' hb)]
  filter_upwards [hrep', hrep] with s hs' hs
  exact hs'.trans hs.symm

end LPP.Busemann
