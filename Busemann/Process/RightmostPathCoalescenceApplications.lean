/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RightmostPathCoalescence
public import Busemann.Process.FiniteBlockFiniteEnergy
public import Busemann.Process.ShiftTopology
public import LPP_Foundations.Probability.TranslationEquiv

/-! Coalescence in the native family and canonical environment. -/

@[expose] public section

open MeasureTheory LPPDifferentiability
open scoped ENNReal BigOperators

namespace LPP.Busemann

/-- Each fixed member of the original native family has coalescing rightmost paths.
The finite-block criterion follows from its backward independence. -/
theorem hasCoalescingRightmostPaths_native_family_of_backward_independence
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (P : Measure ProcessSample)
    (hP : P Set.univ = 1)
    (Bminus Bplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ)
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z : Lattice, P.map (processShift z) = P)
    (hMeasMinus : Measurable
      (fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
        Bminus q.1 q.2.1 q.2.2.1 q.2.2.2))
    (hMeasPlus : Measurable
      (fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
        Bplus q.1 q.2.1 q.2.2.1 q.2.2.2))
    (hBackward : ∀ I : Set Lattice,
      ProbabilityTheory.IndepFun
        (futureVariables g I Bminus Bplus) (pastVariables I) P)
    (h : SupportTilt g) (right : Bool) :
    let C := if right then Bplus h else Bminus h
    is_shift_covariant_cocycle P processShift C →
    recovers_weight_map_ae P processEnvironment C →
    Integrable (C 0 (1, 0)) P → Integrable (C 0 (0, 1)) P →
    HasCoalescingRightmostPaths P C
 := by
  classical
  let : IsProbabilityMeasure P := ⟨hP⟩
  dsimp only
  intro hB hRec hInt₁ hInt₂
  apply hasCoalescingRightmostPaths_of_finite_block_condExp μ hμ hmoment P
    processShift processEnvironment processShift_zero processShift_add
    (fun z => ⟨measurable_processShift z, hShift z⟩) measurable_fst hMarginal
    (fun z x s => by rw [processEnvironment_processShift, environmentTranslationEquiv_apply])
    (if right then Bplus h else Bminus h) hB hRec hInt₁ hInt₂
  exact ae_finset_outside_condExp_pos_native_family_of_backward_independence
    μ g P hP Bminus Bplus hMarginal hMeasMinus hMeasPlus hBackward h right

/-- A forward-measurable canonical cocycle has coalescing rightmost paths;
its finite-block criterion is derived from the original product environment. -/
theorem hasCoalescingRightmostPaths_environmentLaw_of_isForwardMeasurable
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (B : Lattice → Lattice → LPPDifferentiability.Environment → ℝ)
    (hB : is_shift_covariant_cocycle (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) B)
    (hRec : recovers_weight_map_ae (environmentLaw μ)
      (fun ω : LPPDifferentiability.Environment => ω) B)
    (hInt₁ : Integrable (B 0 (1, 0)) (environmentLaw μ))
    (hInt₂ : Integrable (B 0 (0, 1)) (environmentLaw μ))
    (hForward : IsForwardMeasurable B) :
    HasCoalescingRightmostPaths (environmentLaw μ) B
 := by
  classical
  apply hasCoalescingRightmostPaths_of_finite_block_condExp μ hμ hmoment
    (environmentLaw μ) (fun z ω => environmentTranslationEquiv z ω) id
    (fun ω => by funext x; simp [environmentTranslationEquiv_apply])
    (fun z w ω => by funext x; simp [environmentTranslationEquiv_apply, add_comm, add_left_comm])
    (fun z => measurePreserving_environmentTranslationEquiv μ z)
    measurable_id (by simp) (fun z x ω => environmentTranslationEquiv_apply z ω x)
    B hB hRec hInt₁ hInt₂
  exact ae_finset_outside_condExp_pos_environmentLaw_of_isForwardMeasurable μ B hForward

end LPP.Busemann
