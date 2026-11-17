/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import ProbabilityBasics.Analysis.JointHilbertApproximation
import Mathlib.Tactic

/-! Function-level L¹ approximation by a joint invariant and bounded coboundaries. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityBasics

private theorem norm_coboundary_difference_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E →L[ℝ] E) (hU : ‖U‖ ≤ 1) (a b : E) :
    ‖(a - U a) - (b - U b)‖ ≤ 2 * ‖a - b‖ := by
  have hIdentity : (a - U a) - (b - U b) = (a - b) - U (a - b) := by
    rw [map_sub]
    abel
  rw [hIdentity]
  have hBound : ‖U (a - b)‖ ≤ ‖a - b‖ := by
    simpa only [one_mul] using U.le_of_opNorm_le hU (a - b)
  exact (norm_sub_le (a - b) (U (a - b))).trans (by linarith only [hBound])

private theorem integral_abs_lp_two_le_norm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Lp ℝ (2 : ℝ≥0∞) P) : (∫ s, |V s| ∂P) ≤ ‖V‖ := by
  have hInt : Integrable V P := (Lp.memLp V).integrable (by norm_num)
  calc
    (∫ s, |V s| ∂P) = ‖hInt.toL1 V‖ := by
      simpa only [Real.norm_eq_abs] using (L1.norm_of_fun_eq_integral_norm hInt).symm
    _ = (eLpNorm V 1 P).toReal := by
      exact Lp.norm_toLp V (memLp_one_iff_integrable.mpr hInt)
    _ ≤ (eLpNorm V 2 P).toReal := by
      exact ENNReal.toReal_mono (Lp.memLp V).eLpNorm_ne_top
        (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    _ = ‖V‖ := (Lp.norm_def V).symm

private theorem comp_representative_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : Ω → Ω) (hτ : MeasurePreserving τ P P)
    (V : Lp ℝ (2 : ℝ≥0∞) P) (φ : Ω → ℝ) (hφ : (V : Ω → ℝ) =ᵐ[P] φ) :
    (Lp.compMeasurePreserving τ hτ V : Ω → ℝ) =ᵐ[P] fun s => φ (τ s) := by
  filter_upwards [Lp.coeFn_compMeasurePreserving V hτ,
    hτ.quasiMeasurePreserving.ae_eq_comp hφ] with s hs hφs
  simp only [Function.comp_apply] at hs hφs
  exact hs.trans hφs

/-- Every integrable real function on a probability space is approximated in L¹
by a measurable integrable joint invariant and two coboundaries with globally
bounded measurable coefficients. This is the dense good class in Krengel,
Ergodic Theorems, §6.2 Theorem 2.8. No commutation or extra moment of the input is required. -/
theorem exists_l1_joint_invariant_bounded_coboundary_approx
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Fin 2 → Ω → Ω)
    (hT : ∀ i : Fin 2, MeasurePreserving (T i) P P)
    (f : Ω → ℝ) (hf : Integrable f P)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g φ0 φ1 : Ω → ℝ) (M0 M1 : ℝ),
      Measurable g ∧ Integrable g P ∧
      (∀ i : Fin 2, ∀ᵐ s ∂P, g (T i s) = g s) ∧
      Measurable φ0 ∧ Measurable φ1 ∧
      0 ≤ M0 ∧ 0 ≤ M1 ∧
      (∀ s, |φ0 s| ≤ M0) ∧ (∀ s, |φ1 s| ≤ M1) ∧
      (∫ s, |f s - (g s + (φ0 s - φ0 (T 0 s)) +
        (φ1 s - φ1 (T 1 s)))| ∂P) < ε := by
  classical
  have hQuarter : 0 < ε / 4 := by positivity
  have hSixteenth : 0 < ε / 16 := by positivity
  -- Approximate the original merely integrable function in L¹ first.
  obtain ⟨Q1, hQ1⟩ :=
    (Lp.simpleFunc.denseRange (E := ℝ) (p := (1 : ℝ≥0∞)) (μ := P) (by norm_num)).exists_dist_lt
      (hf.toL1 f) hQuarter
  let q : SimpleFunc Ω ℝ := Lp.simpleFunc.toSimpleFunc Q1
  have hq1 : MemLp q (1 : ℝ≥0∞) P := Lp.simpleFunc.memLp Q1
  have hq2 : MemLp q (2 : ℝ≥0∞) P := q.memLp_of_isFiniteMeasure 2 P
  have hqInt : Integrable q P := hq1.integrable (by norm_num)
  have hFirstError : (∫ s, |f s - q s| ∂P) < ε / 4 := by
    have hIntegral : (∫ s, |f s - q s| ∂P) = dist (hf.toL1 f) (Q1 : Lp ℝ 1 P) := by
      rw [L1.dist_eq_integral_dist]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toL1, Lp.simpleFunc.toSimpleFunc_eq_toFun Q1] with s hfs hqs
      simp only [dist_eq_norm, Real.norm_eq_abs]
      rw [hfs, ← hqs]
    rw [hIntegral]
    exact hQ1
  let Q : Lp ℝ (2 : ℝ≥0∞) P := hq2.toLp q
  -- Apply the joint Hilbert approximation to genuine L² shift operators.
  let U : Fin 2 → Lp ℝ (2 : ℝ≥0∞) P →L[ℝ] Lp ℝ (2 : ℝ≥0∞) P := fun i =>
    (Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := (2 : ℝ≥0∞)) ℝ (T i) (hT i)).toContinuousLinearMap
  have hU (i : Fin 2) : ‖U i‖ ≤ 1 :=
    (Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := (2 : ℝ≥0∞)) ℝ (T i) (hT i)).norm_toContinuousLinearMap_le
  obtain ⟨G, a0, a1, hG0, hG1, hHilbertError⟩ :=
    exists_joint_fixed_add_coboundaries_approx (U 0) (U 1) (hU 0) (hU 1) Q (ε / 4) hQuarter
  -- Direct simple-function density supplies actual globally bounded coefficients.
  obtain ⟨S0, hS0⟩ :=
    (Lp.simpleFunc.denseRange (E := ℝ) (p := (2 : ℝ≥0∞)) (μ := P) (by norm_num)).exists_dist_lt
      a0 hSixteenth
  obtain ⟨S1, hS1⟩ :=
    (Lp.simpleFunc.denseRange (E := ℝ) (p := (2 : ℝ≥0∞)) (μ := P) (by norm_num)).exists_dist_lt
      a1 hSixteenth
  let V0 : Lp ℝ (2 : ℝ≥0∞) P := S0
  let V1 : Lp ℝ (2 : ℝ≥0∞) P := S1
  let φ0 : Ω → ℝ := Lp.simpleFunc.toSimpleFunc S0
  let φ1 : Ω → ℝ := Lp.simpleFunc.toSimpleFunc S1
  have hφ0meas : Measurable φ0 := Lp.simpleFunc.measurable S0
  have hφ1meas : Measurable φ1 := Lp.simpleFunc.measurable S1
  have hφ0mem : MemLp φ0 (2 : ℝ≥0∞) P := Lp.simpleFunc.memLp S0
  have hφ1mem : MemLp φ1 (2 : ℝ≥0∞) P := Lp.simpleFunc.memLp S1
  obtain ⟨C0, hC0⟩ := (Lp.simpleFunc.toSimpleFunc S0).exists_forall_norm_le
  obtain ⟨C1, hC1⟩ := (Lp.simpleFunc.toSimpleFunc S1).exists_forall_norm_le
  let M0 : ℝ := max C0 0
  let M1 : ℝ := max C1 0
  have hBound0 (s : Ω) : |φ0 s| ≤ M0 := by
    have hNorm : |φ0 s| ≤ C0 := by simpa only [Real.norm_eq_abs] using hC0 s
    exact hNorm.trans (le_max_left C0 0)
  have hBound1 (s : Ω) : |φ1 s| ≤ M1 := by
    have hNorm : |φ1 s| ≤ C1 := by simpa only [Real.norm_eq_abs] using hC1 s
    exact hNorm.trans (le_max_left C1 0)
  -- A fixed L² class has a measurable integrable representative, fixed only AE.
  let g : Ω → ℝ := G
  have hgMeas : Measurable g := (Lp.stronglyMeasurable G).measurable
  have hgInt : Integrable g P := (Lp.memLp G).integrable (by norm_num)
  have hGfixed (i : Fin 2) : U i G = G := by
    fin_cases i
    · exact hG0
    · exact hG1
  have hgInvariant (i : Fin 2) : ∀ᵐ s ∂P, g (T i s) = g s := by
    have hComp := Lp.coeFn_compMeasurePreserving G (hT i)
    change (U i G : Ω → ℝ) =ᵐ[P] G ∘ T i at hComp
    rw [hGfixed i] at hComp
    filter_upwards [hComp] with s hs
    simpa only [Function.comp_apply, g] using hs.symm
  let H : Lp ℝ (2 : ℝ≥0∞) P := G + (V0 - U 0 V0) + (V1 - U 1 V1)
  have hCoeff0 : ‖(a0 - U 0 a0) - (V0 - U 0 V0)‖ < 2 * (ε / 16) := by
    have hNear : ‖a0 - V0‖ < ε / 16 := by simpa only [dist_eq_norm] using hS0
    exact (norm_coboundary_difference_le (U 0) (hU 0) a0 V0).trans_lt
      (mul_lt_mul_of_pos_left hNear (by norm_num))
  have hCoeff1 : ‖(a1 - U 1 a1) - (V1 - U 1 V1)‖ < 2 * (ε / 16) := by
    have hNear : ‖a1 - V1‖ < ε / 16 := by simpa only [dist_eq_norm] using hS1
    exact (norm_coboundary_difference_le (U 1) (hU 1) a1 V1).trans_lt
      (mul_lt_mul_of_pos_left hNear (by norm_num))
  have hResidualNorm : ‖Q - H‖ < ε / 2 := by
    have hIdentity : Q - H =
        (Q - (G + (a0 - U 0 a0) + (a1 - U 1 a1))) +
          ((a0 - U 0 a0) - (V0 - U 0 V0)) + ((a1 - U 1 a1) - (V1 - U 1 V1)) := by
      dsimp only [H]
      abel
    rw [hIdentity]
    have hTriangle0 := norm_add_le
      (Q - (G + (a0 - U 0 a0) + (a1 - U 1 a1)))
      ((a0 - U 0 a0) - (V0 - U 0 V0))
    have hTriangle1 := norm_add_le
      ((Q - (G + (a0 - U 0 a0) + (a1 - U 1 a1))) + ((a0 - U 0 a0) - (V0 - U 0 V0)))
      ((a1 - U 1 a1) - (V1 - U 1 V1))
    linarith only [hTriangle0, hTriangle1, hHilbertError, hCoeff0, hCoeff1]
  -- Identify the literal function-level approximation using genuine AE bridges.
  let k : Ω → ℝ := fun s => g s + (φ0 s - φ0 (T 0 s)) + (φ1 s - φ1 (T 1 s))
  have hφ0AE : (V0 : Ω → ℝ) =ᵐ[P] φ0 := (Lp.simpleFunc.toSimpleFunc_eq_toFun S0).symm
  have hφ1AE : (V1 : Ω → ℝ) =ᵐ[P] φ1 := (Lp.simpleFunc.toSimpleFunc_eq_toFun S1).symm
  have hUφ0AE : (U 0 V0 : Ω → ℝ) =ᵐ[P] fun s => φ0 (T 0 s) := by
    change (Lp.compMeasurePreserving (T 0) (hT 0) V0 : Ω → ℝ) =ᵐ[P] _
    exact comp_representative_ae P (T 0) (hT 0) V0 φ0 hφ0AE
  have hUφ1AE : (U 1 V1 : Ω → ℝ) =ᵐ[P] fun s => φ1 (T 1 s) := by
    change (Lp.compMeasurePreserving (T 1) (hT 1) V1 : Ω → ℝ) =ᵐ[P] _
    exact comp_representative_ae P (T 1) (hT 1) V1 φ1 hφ1AE
  have hCob0AE : ((V0 - U 0 V0 : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
      fun s => φ0 s - φ0 (T 0 s) :=
    (Lp.coeFn_sub V0 (U 0 V0)).trans (hφ0AE.sub hUφ0AE)
  have hCob1AE : ((V1 - U 1 V1 : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
      fun s => φ1 s - φ1 (T 1 s) :=
    (Lp.coeFn_sub V1 (U 1 V1)).trans (hφ1AE.sub hUφ1AE)
  have hHAE : (H : Ω → ℝ) =ᵐ[P] k := by
    filter_upwards [Lp.coeFn_add (G + (V0 - U 0 V0)) (V1 - U 1 V1),
      Lp.coeFn_add G (V0 - U 0 V0), hCob0AE, hCob1AE] with s hAdd1 hAdd0 h0s h1s
    simp only [Pi.add_apply] at hAdd1 hAdd0
    calc
      H s = (G + (V0 - U 0 V0)) s + (V1 - U 1 V1) s := hAdd1
      _ = (G s + (V0 - U 0 V0) s) + (V1 - U 1 V1) s := by rw [hAdd0]
      _ = k s := by
        change (G s + (V0 - U 0 V0) s) + (V1 - U 1 V1) s =
          G s + (φ0 s - φ0 (T 0 s)) + (φ1 s - φ1 (T 1 s))
        rw [h0s, h1s]
  have hQAE : (Q : Ω → ℝ) =ᵐ[P] (q : Ω → ℝ) := hq2.coeFn_toLp
  have hResidualAE : ((Q - H : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] fun s => q s - k s :=
    (Lp.coeFn_sub Q H).trans (hQAE.sub hHAE)
  have hSecondError : (∫ s, |q s - k s| ∂P) ≤ ‖Q - H‖ := by
    calc
      (∫ s, |q s - k s| ∂P) = ∫ s, |(Q - H) s| ∂P :=
        integral_congr_ae (hResidualAE.symm.fun_comp abs)
      _ ≤ ‖Q - H‖ := integral_abs_lp_two_le_norm P (Q - H)
  -- Transfer the L² error into L¹ and combine it with the first approximation.
  have hφ0Int : Integrable φ0 P := hφ0mem.integrable (by norm_num)
  have hφ1Int : Integrable φ1 P := hφ1mem.integrable (by norm_num)
  have hφ0TInt : Integrable (fun s => φ0 (T 0 s)) P :=
    (hT 0).integrable_comp_of_integrable hφ0Int
  have hφ1TInt : Integrable (fun s => φ1 (T 1 s)) P :=
    (hT 1).integrable_comp_of_integrable hφ1Int
  have hkInt : Integrable k P := (hgInt.add (hφ0Int.sub hφ0TInt)).add (hφ1Int.sub hφ1TInt)
  refine ⟨g, φ0, φ1, M0, M1, hgMeas, hgInt, hgInvariant, hφ0meas, hφ1meas,
    le_max_right C0 0, le_max_right C1 0, hBound0, hBound1, ?_⟩
  change (∫ s, |f s - k s| ∂P) < ε
  have hPoint (s : Ω) : |f s - k s| ≤ |f s - q s| + |q s - k s| :=
    abs_sub_le (f s) (q s) (k s)
  have hIntegral := integral_mono (hf.sub hkInt).abs
    (((hf.sub hqInt).abs).add ((hqInt.sub hkInt).abs)) hPoint
  simp only [Pi.add_apply] at hIntegral
  rw [integral_add (hf.sub hqInt).abs (hqInt.sub hkInt).abs] at hIntegral
  simp only [Pi.sub_apply] at hIntegral
  linarith only [hIntegral, hFirstError, hSecondError, hResidualNorm, hε]

end ProbabilityBasics
