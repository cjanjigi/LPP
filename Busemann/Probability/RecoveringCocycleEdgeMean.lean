/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving

public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import Busemann.Frozen.Definitions.RandomCocycle
public import Busemann.Frozen.Definitions.RecoveryAE
public import LPP_Foundations.Probability.TranslationEquiv
public import LPP_Foundations.Probability.TranslationErgodic
public import LPP_Foundations.Probability.PassageIntegrable
public import ProbabilityBasics.Probability.BirkhoffErgodic

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped Topology
namespace LPP.Busemann

/-- A deterministic finite axial cocycle slope forces its recovering origin
edge to be integrable and identifies its ordinary mean. The proof uses
bounded truncations of the nonnegative edge-minus-weight defect before
applying Birkhoff to the edge itself. Strong Existence, lm:orig_space,
lines 1090–1092. -/
theorem integrable_origin_edge_and_mean_of_finite_axial_slope
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (C : Lattice → Lattice → Environment → ℝ)
    (hC : is_shift_covariant_cocycle (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) C)
    (hRec : recovers_weight_map_ae (environmentLaw μ)
      (fun ω : Environment => ω) C)
    (i : Fin 2) (a : ℝ)
    (hSlope : ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n : ℕ => C 0 (n • finiteEdgeStep i) ω / (n : ℝ))
        atTop (𝓝 a)) :
    Integrable (fun ω => C 0 (finiteEdgeStep i) ω) (environmentLaw μ) ∧
      (∫ ω, C 0 (finiteEdgeStep i) ω ∂environmentLaw μ) = a := by
  let P : Measure Environment := environmentLaw μ
  let e : Lattice := finiteEdgeStep i
  let T : Lattice → Environment → Environment :=
    fun z ω => environmentTranslationEquiv z ω
  let edge : Environment → ℝ := fun ω => C 0 e ω
  let weight : Environment → ℝ := fun ω => ω 0
  let defect : Environment → ℝ := fun ω => max (edge ω - weight ω) 0
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  have he : e ≠ 0 := by
    rcases hi with hi | hi
    · have h : i = 0 := Fin.ext hi
      subst i
      simp [e, finiteEdgeStep]
    · have h : i = 1 := Fin.ext hi
      subst i
      simp [e, finiteEdgeStep]
  have hzero : ∀ ω : Environment, T 0 ω = ω := by
    intro ω
    ext z
    simp [T, environmentTranslationEquiv_apply]
  have hadd : ∀ (z w : Lattice) (ω : Environment),
      T (z + w) ω = T z (T w ω) := by
    intro z w ω
    ext x
    simp [T, environmentTranslationEquiv_apply, add_comm, add_left_comm]
  have hIter (n : ℕ) (ω : Environment) :
      (T e)^[n] ω = T (n • e) ω := by
    induction n with
    | zero => simp only [Function.iterate_zero_apply, zero_nsmul, hzero ω]
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        simpa only [succ_nsmul, add_comm] using (hadd e (n • e) ω).symm
  have hShift : MeasurePreserving (T e) P P := by
    simpa [P, T] using measurePreserving_environmentTranslationEquiv μ e
  have hTRepresentation : T e =
      (fun ω : Environment => fun z : Lattice => ω (e + z)) := by
    funext ω
    ext z
    simp [T, environmentTranslationEquiv_apply]
  have hErg : Ergodic (T e) P := by
    rw [hTRepresentation]
    simpa [P] using ergodic_environment_translation μ e he
  have hMeasEdge : Measurable edge := by
    dsimp [edge, e]
    exact hC.1.comp ((measurable_const.prodMk measurable_const).prodMk measurable_id)
  have hMeasWeight : Measurable weight := by
    exact measurable_environment_eval 0
  have hMeasDefect : Measurable defect := by
    exact (hMeasEdge.sub hMeasWeight).max measurable_const
  have hRecovery : ∀ᵐ ω ∂P,
      min (C 0 ((1 : ℤ), (0 : ℤ)) ω) (C 0 ((0 : ℤ), (1 : ℤ)) ω) = weight ω := by
    filter_upwards [hRec] with ω hω
    exact hω 0
  have hLowerEdge : ∀ᵐ ω ∂P, weight ω ≤ edge ω := by
    filter_upwards [hRecovery] with ω hω
    have hmin :
        min (C 0 ((1 : ℤ), (0 : ℤ)) ω) (C 0 ((0 : ℤ), (1 : ℤ)) ω) ≤
          C 0 (finiteEdgeStep i) ω := by
      rcases hi with hi | hi
      · have h : i = 0 := Fin.ext hi
        subst i
        have hstep : finiteEdgeStep (0 : Fin 2) = ((1 : ℤ), (0 : ℤ)) := by
          simp [finiteEdgeStep]
        rw [hstep]
        exact min_le_left _ _
      · have h : i = 1 := Fin.ext hi
        subst i
        have hstep : finiteEdgeStep (1 : Fin 2) = ((0 : ℤ), (1 : ℤ)) := by
          simp [finiteEdgeStep]
        rw [hstep]
        exact min_le_right _ _
    rw [← hω]
    simpa [finiteEdgeStep, edge, e] using hmin
  have hDefectNonneg : ∀ ω, 0 ≤ defect ω := by
    intro ω
    exact le_max_right _ _
  have hDefectEq : defect =ᵐ[P] (fun ω => edge ω - weight ω) := by
    filter_upwards [hLowerEdge] with ω hω
    simp only [defect, edge, weight, max_eq_left (sub_nonneg.mpr hω)]
  have hTel : ∀ᵐ ω ∂P, ∀ n : ℕ,
      C 0 (n • e) ω = birkhoffSum (T e) edge n ω := by
    have hCov : ∀ᵐ ω ∂P, ∀ n : ℕ,
        C (n • e) (n • e + e) ω = edge ((T e)^[n] ω) := by
      apply ae_all_iff.mpr
      intro n
      have hcov := hC.2.1 0 e (n • e)
      filter_upwards [hcov] with ω hω
      simpa only [zero_add, add_comm e (n • e), edge, hIter n ω] using hω
    filter_upwards [hC.2.2, hCov] with ω haddc hcov
    intro n
    induction n with
    | zero =>
        have hz := haddc 0 0 0
        change C 0 0 ω + C 0 0 ω = C 0 0 ω at hz
        simp only [zero_nsmul, birkhoffSum_zero_apply]
        linarith only [hz]
    | succ n ih =>
        rw [birkhoffSum_succ_apply, ← ih, hIter n ω]
        have hadd := haddc 0 (n • e) (n • e + e)
        change C 0 (n • e) ω + C (n • e) (n • e + e) ω =
          C 0 (n • e + e) ω at hadd
        rw [hcov n] at hadd
        rw [hIter n ω] at hadd
        simpa only [succ_nsmul] using hadd.symm
  have hSlopeAvg : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => birkhoffAverage ℝ (T e) edge n ω) atTop (𝓝 a) := by
    have hEq (n : ℕ) :
        (fun ω => C 0 (n • e) ω / (n : ℝ)) =ᵐ[P]
          birkhoffAverage ℝ (T e) edge n := by
      filter_upwards [hTel] with ω hω
      simp only [hω n, birkhoffAverage, smul_eq_mul, div_eq_mul_inv, mul_comm]
    filter_upwards [hSlope, ae_all_iff.mpr hEq] with ω hs heq
    have hfun :
        (fun n : ℕ => C 0 (n • e) ω / (n : ℝ)) =
          (fun n => birkhoffAverage ℝ (T e) edge n ω) := funext heq
    rw [← hfun]
    exact hs
  have hWeightInt : Integrable weight P := by
    exact (integrable_environment_eval μ hμ 0).congr (Filter.Eventually.of_forall fun _ => rfl)
  have hWeightLimit : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => birkhoffAverage ℝ (T e) weight n ω) atTop
        (𝓝 (∫ ω, weight ω ∂P)) :=
    ae_tendsto_birkhoffAverage_integral_of_ergodic hErg hMeasWeight hWeightInt
  have hDefectAverageEq (n : ℕ) :
      birkhoffAverage ℝ (T e) defect n =ᵐ[P]
        (birkhoffAverage ℝ (T e) edge n - birkhoffAverage ℝ (T e) weight n) := by
    filter_upwards [hShift.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq
      ℝ hDefectEq n] with ω hω
    rw [hω]
    exact birkhoffAverage_sub_apply n ω
  have hDefectAverageLimit : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => birkhoffAverage ℝ (T e) defect n ω) atTop
        (𝓝 (a - ∫ ω, weight ω ∂P)) := by
    filter_upwards [hSlopeAvg, hWeightLimit, ae_all_iff.mpr hDefectAverageEq]
      with ω hEdge hWeight hEq
    have hfun :
        (fun n : ℕ => birkhoffAverage ℝ (T e) defect n ω) =
          (fun n => birkhoffAverage ℝ (T e) edge n ω -
            birkhoffAverage ℝ (T e) weight n ω) := funext hEq
    rw [hfun]
    exact hEdge.sub hWeight
  let trunc : ℕ → Environment → ℝ :=
    fun k ω => min (defect ω) ((k : ℝ) + 1)
  have hTruncMeas (k : ℕ) : Measurable (trunc k) := by
    exact hMeasDefect.min measurable_const
  have hTruncLe (k : ℕ) (ω : Environment) : trunc k ω ≤ defect ω :=
    min_le_left _ _
  have hTruncNonneg (k : ℕ) (ω : Environment) : 0 ≤ trunc k ω :=
    le_min (hDefectNonneg ω) (by positivity)
  have hTruncInt (k : ℕ) : Integrable (trunc k) P := by
    apply (integrable_const ‖(k : ℝ) + 1‖).mono' (hTruncMeas k).aestronglyMeasurable
    apply ae_of_all
    intro ω
    have habs : |trunc k ω| ≤ (k : ℝ) + 1 :=
      abs_le.mpr ⟨by linarith [hTruncNonneg k ω], min_le_right _ _⟩
    simpa [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity)] using habs
  have hTruncAverageLe (k n : ℕ) (ω : Environment) :
      birkhoffAverage ℝ (T e) (trunc k) n ω ≤
        birkhoffAverage ℝ (T e) defect n ω := by
    have hsum :
        birkhoffSum (T e) (trunc k) n ω ≤ birkhoffSum (T e) defect n ω := by
      unfold birkhoffSum
      apply Finset.sum_le_sum
      intro j _
      exact hTruncLe k ((T e)^[j] ω)
    simpa only [birkhoffAverage, smul_eq_mul] using
      (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg n)))
  have hTruncIntegralBound (k : ℕ) :
      (∫ ω, trunc k ω ∂P) ≤ a - ∫ ω, weight ω ∂P := by
    have hTruncLimit : ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => birkhoffAverage ℝ (T e) (trunc k) n ω) atTop
          (𝓝 (∫ ω, trunc k ω ∂P)) :=
      ae_tendsto_birkhoffAverage_integral_of_ergodic hErg (hTruncMeas k) (hTruncInt k)
    have hBoundAE : ∀ᵐ ω ∂P,
        (∫ ω, trunc k ω ∂P) ≤ a - ∫ ω, weight ω ∂P := by
      filter_upwards [hTruncLimit, hDefectAverageLimit] with ω hTrunc hDefect
      exact le_of_tendsto_of_tendsto hTrunc hDefect
        (Eventually.of_forall (fun n => hTruncAverageLe k n ω))
    by_contra hnot
    have hfalse : ∀ᵐ ω ∂P, False := hBoundAE.mono (fun _ h => hnot h)
    have hzero : P Set.univ = 0 := by
      simpa using (ae_iff.mp hfalse)
    have hprob : P Set.univ = 1 := by simp [P]
    rw [hzero] at hprob
    norm_num at hprob
  have hTruncLIntegralEq (k : ℕ) :
      ENNReal.ofReal (∫ ω, trunc k ω ∂P) =
        ∫⁻ ω, ENNReal.ofReal (trunc k ω) ∂P :=
    ofReal_integral_eq_lintegral_ofReal (hTruncInt k)
      (ae_of_all _ (hTruncNonneg k))
  have hTruncLIntegralMonotone : ∀ᵐ ω ∂P,
      Monotone (fun k : ℕ => ENNReal.ofReal (trunc k ω)) := by
    apply ae_of_all
    intro ω m n hmn
    apply ENNReal.ofReal_le_ofReal
    have hmn' : m + 1 ≤ n + 1 := Nat.add_le_add_right hmn 1
    exact min_le_min_left _ (by exact_mod_cast hmn')
  have hTruncLIntegralPointwise : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => ENNReal.ofReal (trunc k ω)) atTop
        (𝓝 (ENNReal.ofReal (defect ω))) := by
    apply ae_of_all
    intro ω
    have hEventually : ∀ᶠ k : ℕ in atTop, trunc k ω = defect ω := by
      filter_upwards [eventually_ge_atTop (⌈defect ω⌉₊)] with k hk
      have hceil : defect ω ≤ ((⌈defect ω⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have hk' : ((⌈defect ω⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hle : defect ω ≤ (k : ℝ) + 1 := le_trans hceil (by linarith)
      simp [trunc, min_eq_left hle]
    have hEventuallyReal :
        (fun k : ℕ => ENNReal.ofReal (trunc k ω)) =ᶠ[atTop]
          fun _ => ENNReal.ofReal (defect ω) := by
      filter_upwards [hEventually] with k hk
      rw [hk]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => ENNReal.ofReal (defect ω))
      atTop (𝓝 (ENNReal.ofReal (defect ω)))).congr' hEventuallyReal.symm
  have hMCT : Tendsto (fun k : ℕ => ∫⁻ ω, ENNReal.ofReal (trunc k ω) ∂P)
      atTop (𝓝 (∫⁻ ω, ENNReal.ofReal (defect ω) ∂P)) :=
    lintegral_tendsto_of_tendsto_of_monotone
      (fun k => (hTruncMeas k).aemeasurable.ennreal_ofReal)
      hTruncLIntegralMonotone hTruncLIntegralPointwise
  have hLIntegralBound : ∀ k : ℕ,
      (∫⁻ ω, ENNReal.ofReal (trunc k ω) ∂P) ≤
        ENNReal.ofReal (a - ∫ ω, weight ω ∂P) := by
    intro k
    rw [← hTruncLIntegralEq k]
    exact ENNReal.ofReal_le_ofReal (hTruncIntegralBound k)
  have hDefectLIntegralBound :
      (∫⁻ ω, ENNReal.ofReal (defect ω) ∂P) ≤
        ENNReal.ofReal (a - ∫ ω, weight ω ∂P) :=
    le_of_tendsto' hMCT hLIntegralBound
  have hDefectLIntegralNeTop :
      (∫⁻ ω, ENNReal.ofReal (defect ω) ∂P) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hDefectLIntegralBound
  have hDefectInt : Integrable defect P :=
    (lintegral_ofReal_ne_top_iff_integrable hMeasDefect.aestronglyMeasurable
      (ae_of_all _ hDefectNonneg)).mp hDefectLIntegralNeTop
  have hEdgeEq : edge =ᵐ[P] (fun ω => weight ω + defect ω) := by
    filter_upwards [hDefectEq] with ω hω
    linarith
  have hEdgeInt : Integrable edge P :=
    (hWeightInt.add hDefectInt).congr hEdgeEq.symm
  have hEdgeLimit : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => birkhoffAverage ℝ (T e) edge n ω) atTop
        (𝓝 (∫ ω, edge ω ∂P)) :=
    ae_tendsto_birkhoffAverage_integral_of_ergodic hErg hMeasEdge hEdgeInt
  have hMeanEq : a = ∫ ω, edge ω ∂P := by
    have hMeanAE : ∀ᵐ ω ∂P, a = ∫ ω, edge ω ∂P := by
      filter_upwards [hSlopeAvg, hEdgeLimit] with ω hs he
      exact tendsto_nhds_unique hs he
    by_contra hnot
    have hfalse : ∀ᵐ ω ∂P, False := hMeanAE.mono (fun _ heq => hnot heq)
    have hzero : P Set.univ = 0 := by
      simpa using (ae_iff.mp hfalse)
    have hprob : P Set.univ = 1 := by simp [P]
    rw [hzero] at hprob
    norm_num at hprob
  refine ⟨?_, hMeanEq.symm⟩
  simpa [edge, e] using hEdgeInt

end LPP.Busemann
