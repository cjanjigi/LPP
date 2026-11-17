/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.LatticeInvariantConditionalDrifts
public import Busemann.Frozen.Definitions.LatticeInvariantSigma
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import ProbabilityBasics.Probability.BirkhoffInvariantSetIntegrals
import Mathlib.Tactic

/-! Conditional means for a directional shift and the full shift action. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped Topology

namespace LPP.Busemann

/-- A unit increment has the same conditional mean under its unit-shift
invariants as under the full signed-action invariants. This is the directional
bridge from JR arXiv:1810.03580v3, Appendix B, Lemma B.4 and (B.2), source
reading lines 2688–2710. -/
theorem directional_condExp_eq_full_action_condExp_of_action
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω)
    (hzero : ∀ s : Ω, T 0 s = s)
    (hadd : ∀ (z w : Lattice) (s : Ω), T (z + w) s = T z (T w s))
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (hInt : ∀ x y, Integrable (B x y) P) :
    let mΩ0 : MeasurableSpace Ω := inferInstance
    let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
    let J : Fin 2 → MeasurableSpace Ω := fun i =>
      @MeasurableSpace.invariants Ω mΩ0 (T (finiteEdgeStep i))
    letI : MeasurableSpace Ω := mΩ0
    ∀ i : Fin 2,
      P[B 0 (finiteEdgeStep i) | J i] =ᵐ[P]
        P[B 0 (finiteEdgeStep i) | I] := by
  classical
  let mΩ0 : MeasurableSpace Ω := inferInstance
  let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
  let J : Fin 2 → MeasurableSpace Ω := fun i =>
    @MeasurableSpace.invariants Ω mΩ0 (T (finiteEdgeStep i))
  let : MeasurableSpace Ω := mΩ0
  change ∀ i : Fin 2, P[B 0 (finiteEdgeStep i) | J i] =ᵐ[P]
    P[B 0 (finiteEdgeStep i) | I]
  obtain ⟨u, ⟨huData, huInv⟩, huFull⟩ :=
    exists_full_action_directional_drifts_condExp_of_action
      P T hzero hadd hShift B hB hInt
  intro i
  let e : Lattice := finiteEdgeStep i
  let U : Ω → Ω := T e
  obtain ⟨v, hvm, hvi, hvInv, hvL1, hvMean⟩ :=
    ProbabilityBasics.exists_birkhoffL1_invariant_set_integrals P U (hShift e)
      (B 0 e) (hInt 0 e)
  have hIter (n : ℕ) (s : Ω) : U^[n] s = T (n • e) s := by
    induction n with
    | zero => simp only [Function.iterate_zero_apply, zero_nsmul, hzero s]
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      change T e (T (n • e) s) = _
      simpa only [succ_nsmul, add_comm] using (hadd e (n • e) s).symm
  have htel : ∀ᵐ s ∂P, ∀ n : ℕ,
      B 0 (n • e) s = birkhoffSum U (B 0 e) n s := by
    have hcov : ∀ᵐ s ∂P, ∀ n : ℕ,
        B (n • e) (n • e + e) s = B 0 e (T (n • e) s) := by
      apply ae_all_iff.mpr
      intro n
      simpa only [zero_add, add_comm e (n • e)] using hB.2.1 0 e (n • e)
    filter_upwards [hB.2.2, hcov] with s hs hc
    intro n
    induction n with
    | zero =>
      have hz := hs 0 0 0
      change B 0 0 s + B 0 0 s = B 0 0 s at hz
      simp only [zero_nsmul, birkhoffSum_zero_apply]
      linarith only [hz]
    | succ n ih =>
      rw [birkhoffSum_succ_apply, ← ih, hIter]
      have hadd := hs 0 (n • e) (n • e + e)
      change B 0 (n • e) s + B (n • e) (n • e + e) s = B 0 (n • e + e) s at hadd
      rw [hc n] at hadd
      simpa only [succ_nsmul] using hadd.symm
  have heq (n : ℕ) : (fun s => B 0 (n • e) s / (n : ℝ)) =ᵐ[P]
      birkhoffAverage ℝ U (B 0 e) n := by
    filter_upwards [htel] with s hs
    simp only [hs n, birkhoffAverage, smul_eq_mul, div_eq_mul_inv, mul_comm]
  let X : ℕ → Ω → ℝ := fun n s => B 0 (n • e) s / (n : ℝ)
  have hXint (n : ℕ) : Integrable (X n) P := (hInt 0 (n • e)).div_const (n : ℝ)
  have huInt : Integrable (u i) P := (huData i).2.1
  have hXv : Tendsto (fun n : ℕ => ∫ s, |X n s - v s| ∂P) atTop (𝓝 0) := by
    apply hvL1.congr'
    filter_upwards [] with n
    apply integral_congr_ae
    filter_upwards [heq n] with s hs
    change |birkhoffAverage ℝ U (B 0 e) n s - v s| =
      |B 0 (n • e) s / (n : ℝ) - v s|
    rw [hs]
  have hXu : Tendsto (fun n : ℕ => ∫ s, |X n s - u i s| ∂P) atTop (𝓝 0) :=
    (huData i).2.2.2.2
  have hdiff : Integrable (fun s => |v s - u i s|) P := by
    simpa only [Pi.sub_apply] using (hvi.sub huInt).abs
  have hbound (n : ℕ) : (∫ s, |v s - u i s| ∂P) ≤
      (∫ s, |X n s - v s| ∂P) + ∫ s, |X n s - u i s| ∂P := by
    have h1 : Integrable (fun s => |X n s - v s|) P := by
      simpa only [Pi.sub_apply] using ((hXint n).sub hvi).abs
    have h2 : Integrable (fun s => |X n s - u i s|) P := by
      simpa only [Pi.sub_apply] using ((hXint n).sub huInt).abs
    have hh := integral_mono hdiff (h1.add h2) (fun s => by
      have h := abs_sub_le (v s) (X n s) (u i s)
      simpa only [abs_sub_comm (v s) (X n s), Pi.add_apply] using h)
    simpa only [Pi.add_apply, integral_add h1 h2] using hh
  have hlim : Tendsto (fun n : ℕ => (∫ s, |X n s - v s| ∂P) +
      ∫ s, |X n s - u i s| ∂P) atTop (𝓝 0) := by
    simpa only [add_zero] using hXv.add hXu
  have hzero : (∫ s, |v s - u i s| ∂P) = 0 := by
    have hle : (∫ s, |v s - u i s| ∂P) ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hbound)
    exact le_antisymm hle (integral_nonneg fun s => abs_nonneg _)
  have hvu : v =ᵐ[P] u i := by
    have hh := (integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all P fun s => abs_nonneg (v s - u i s)) hdiff).mp hzero
    filter_upwards [hh] with s hs
    exact sub_eq_zero.mp (abs_eq_zero.mp hs)
  have hm : J i ≤ mΩ0 := MeasurableSpace.invariants_le (T e)
  let : IsFiniteMeasure (P.trim hm) := inferInstance
  let : SigmaFinite (P.trim hm) := inferInstance
  have huJ : Measurable[J i] (u i) := by
    intro A hA
    apply MeasurableSpace.measurableSet_invariants.mpr
    refine ⟨(huData i).1 hA, ?_⟩
    ext s
    change u i (T e s) ∈ A ↔ u i s ∈ A
    rw [huInv i e s]
  have huMean (A : Set Ω) (hA : MeasurableSet[J i] A) :
      (∫ s in A, u i s ∂P) = ∫ s in A, B 0 e s ∂P := by
    obtain ⟨hAm, hAi⟩ := MeasurableSpace.measurableSet_invariants.mp hA
    calc
      _ = ∫ s in A, v s ∂P := integral_congr_ae (ae_restrict_of_ae hvu.symm)
      _ = ∫ s in A, B 0 e s ∂P := hvMean A hAm hAi
  have huJCE : u i =ᵐ[P] P[B 0 e | J i] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hm (hInt 0 e)
    · intro A _ _
      exact huInt.integrableOn
    · intro A hA _
      exact huMean A hA
    · exact huJ.aestronglyMeasurable
  exact huJCE.symm.trans (huFull i)

end LPP.Busemann
