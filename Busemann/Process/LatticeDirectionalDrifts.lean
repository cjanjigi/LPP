/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.RandomCocycle
public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import ProbabilityBasics.Probability.BirkhoffL1
import ProbabilityBasics.Probability.IdentDistribSublinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Directional drifts for a full lattice action

An arbitrary measure-preserving lattice action and an integrable shift-covariant
cocycle have random directional drifts with literal displacement limits, L1
convergence, and exactly invariant representatives.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set LPPDifferentiability
open scoped Topology

namespace LPP.Busemann

private theorem iterate_action
    {Ω : Type*} (T : Lattice → Ω → Ω)
    (hzero : ∀ s : Ω, T 0 s = s)
    (hadd : ∀ (z w : Lattice) (s : Ω), T (z + w) s = T z (T w s))
    (e : Lattice) (n : ℕ) (s : Ω) :
    (T e)^[n] s = T (n • e) s := by
  induction n with
  | zero => simp only [Function.iterate_zero_apply, zero_nsmul, hzero s]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simpa only [succ_nsmul, add_comm] using (hadd e (n • e) s).symm

private theorem exact_invariant_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : Lattice → Ω → Ω)
    (hzero : ∀ s : Ω, T 0 s = s)
    (hadd : ∀ (z w : Lattice) (s : Ω), T (z + w) s = T z (T w s))
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (v : Ω → ℝ) (hvm : Measurable v)
    (hinv : ∀ z : Lattice, ∀ᵐ s ∂P, v (T z s) = v s) :
    ∃ u : Ω → ℝ, Measurable u ∧ u =ᵐ[P] v ∧
      ∀ (z : Lattice) (s : Ω), u (T z s) = u s := by
  classical
  let C : Set Ω := {s | ∀ z w : Lattice, v (T z s) = v (T w s)}
  have hCm : MeasurableSet C := by
    simp only [C, Set.ofPred_forall]
    exact MeasurableSet.iInter fun z => MeasurableSet.iInter fun w =>
      measurableSet_eq_fun (hvm.comp (hShift z).measurable)
        (hvm.comp (hShift w).measurable)
  have hCae : ∀ᵐ s ∂P, s ∈ C := by
    filter_upwards [ae_all_iff.mpr hinv] with s hs
    exact fun z w => (hs z).trans (hs w).symm
  have hCforward (z : Lattice) (s : Ω) (hs : s ∈ C) : T z s ∈ C := by
    intro x y
    rw [← hadd x z s, ← hadd y z s]
    exact hs (x + z) (y + z)
  have hTinv (z : Lattice) (s : Ω) : T (-z) (T z s) = s := by
    rw [← hadd (-z) z s, neg_add_cancel, hzero s]
  have hCiff (z : Lattice) (s : Ω) : T z s ∈ C ↔ s ∈ C := by
    constructor
    · intro hs
      have hback := hCforward (-z) (T z s) hs
      rw [hTinv z s] at hback
      exact hback
    · exact hCforward z s
  let u : Ω → ℝ := C.indicator v
  have hueq : u =ᵐ[P] v := by
    filter_upwards [hCae] with s hs
    exact Set.indicator_of_mem hs v
  refine ⟨u, hvm.indicator hCm, hueq, ?_⟩
  intro z s
  change C.indicator v (T z s) = C.indicator v s
  by_cases hs : s ∈ C
  · rw [Set.indicator_of_mem ((hCiff z s).mpr hs), Set.indicator_of_mem hs]
    simpa only [hzero s] using hs z 0
  · have hnot : T z s ∉ C := fun h => hs ((hCiff z s).mp h)
    rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hs]

private theorem exists_directional_drift_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω)
    (hzero : ∀ s : Ω, T 0 s = s)
    (hadd : ∀ (z w : Lattice) (s : Ω), T (z + w) s = T z (T w s))
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (hInt : ∀ x y, Integrable (B x y) P) (e : Lattice) :
    ∃ v : Ω → ℝ, Measurable v ∧ Integrable v P ∧
      (∀ᵐ s ∂P, Tendsto (fun n : ℕ => B 0 (n • e) s / (n : ℝ))
        atTop (𝓝 (v s))) ∧
      (∫ s, v s ∂P) = ∫ s, B 0 e s ∂P ∧
      Tendsto (fun n : ℕ => ∫ s, |B 0 (n • e) s / (n : ℝ) - v s| ∂P)
        atTop (𝓝 0) ∧
      (∀ z : Lattice, ∀ᵐ s ∂P, v (T z s) = v s) := by
  have hmeas (x y : Lattice) : Measurable (B x y) := by
    have hmap : Measurable (fun s : Ω => ((x, y), s)) :=
      measurable_const.prodMk measurable_id
    exact hB.1.comp hmap
  -- Actual additive increments telescope to the actual Birkhoff sums.
  have htel : ∀ᵐ s ∂P, ∀ n : ℕ,
      B 0 (n • e) s = birkhoffSum (T e) (B 0 e) n s := by
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
      rw [birkhoffSum_succ_apply, ← ih, iterate_action T hzero hadd e n s]
      have hadd := hs 0 (n • e) (n • e + e)
      change B 0 (n • e) s + B (n • e) (n • e + e) s =
        B 0 (n • e + e) s at hadd
      rw [hc n] at hadd
      simpa only [succ_nsmul] using hadd.symm
  have heq (n : ℕ) : (fun s => B 0 (n • e) s / (n : ℝ)) =ᵐ[P]
      birkhoffAverage ℝ (T e) (B 0 e) n := by
    filter_upwards [htel] with s hs
    simp only [hs n, birkhoffAverage, smul_eq_mul, div_eq_mul_inv, mul_comm]
  obtain ⟨v, hvm, hvi, hvc, _, hvmean, hvL1⟩ :=
    exists_birkhoffL1 (hShift e) (hmeas 0 e) (hInt 0 e)
  have hvLiteral : ∀ᵐ s ∂P, Tendsto (fun n : ℕ => B 0 (n • e) s / (n : ℝ))
      atTop (𝓝 (v s)) := by
    filter_upwards [hvc, ae_all_iff.mpr heq] with s hc hs
    have hfun : (fun n : ℕ => B 0 (n • e) s / (n : ℝ)) =
        (fun n => birkhoffAverage ℝ (T e) (B 0 e) n s) := funext hs
    rw [hfun]
    exact hc
  have hIntegral (n : ℕ) :
      (∫ s, |B 0 (n • e) s / (n : ℝ) - v s| ∂P) =
        ∫ s, |birkhoffAverage ℝ (T e) (B 0 e) n s - v s| ∂P := by
    apply integral_congr_ae
    filter_upwards [heq n] with s hs
    rw [hs]
  have hvLiteralL1 : Tendsto (fun n : ℕ => ∫ s,
      |B 0 (n • e) s / (n : ℝ) - v s| ∂P) atTop (𝓝 0) := by
    simpa only [hIntegral] using hvL1
  refine ⟨v, hvm, hvi, hvLiteral, hvmean, hvLiteralL1, ?_⟩
  intro z
  -- Identically distributed shifted boundary increments vanish after division by n.
  have hboundary : ∀ᵐ s ∂P, Tendsto (fun n : ℕ =>
      B 0 z (T (n • e) s) / (n : ℝ)) atTop (𝓝 0) := by
    apply ae_tendsto_identDistrib_div_nat (hInt 0 z)
    intro n
    refine ⟨((hmeas 0 z).comp (hShift (n • e)).measurable).aemeasurable,
      (hmeas 0 z).aemeasurable, ?_⟩
    change P.map ((B 0 z) ∘ T (n • e)) = P.map (B 0 z)
    rw [← Measure.map_map (hmeas 0 z) (hShift (n • e)).measurable,
      (hShift (n • e)).map_eq]
  -- Additivity and covariance relate the translated ray limits by boundary terms.
  have hcomm (n : ℕ) : ∀ᵐ s ∂P,
      B 0 (n • e) (T z s) =
        B 0 (n • e) s + B 0 z (T (n • e) s) - B 0 z s := by
    filter_upwards [hB.2.2, hB.2.1 0 (n • e) z, hB.2.1 0 z (n • e)]
      with s hs hc₁ hc₂
    have ha := hs 0 z (z + n • e)
    have hb := hs 0 (n • e) (z + n • e)
    simp only [zero_add] at hc₁ hc₂
    rw [add_comm (n • e) z] at hc₁
    linarith only [ha, hb, hc₁, hc₂]
  have hshiftConv := (hShift z).quasiMeasurePreserving.ae hvLiteral
  filter_upwards [hvLiteral, hshiftConv, hboundary, ae_all_iff.mpr hcomm]
    with s hc hcs hbnd hcomms
  have hfixed : Tendsto (fun n : ℕ => B 0 z s / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (B 0 z s)
  have hrelation (n : ℕ) : B 0 (n • e) (T z s) / (n : ℝ) =
      B 0 (n • e) s / (n : ℝ) + B 0 z (T (n • e) s) / (n : ℝ) -
        B 0 z s / (n : ℝ) := by
    rw [hcomms n]
    ring
  have hsame : Tendsto (fun n : ℕ => B 0 (n • e) (T z s) / (n : ℝ))
      atTop (𝓝 (v s)) := by
    simpa only [← hrelation, add_zero, sub_zero] using (hc.add hbnd).sub hfixed
  exact tendsto_nhds_unique hcs hsame

/-- An arbitrary measurable probability space with a measure-preserving full lattice action and
an integrable shift-covariant cocycle has directional drifts with literal limits, L1 convergence,
and exactly invariant representatives. This is JR1810.03580v3, Appendix B, Lemma B.4. -/
theorem exists_full_action_directional_drifts_of_action
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω)
    (hzero : ∀ s : Ω, T 0 s = s)
    (hadd : ∀ (z w : Lattice) (s : Ω), T (z + w) s = T z (T w s))
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (hInt : ∀ x y, Integrable (B x y) P) :
    ∃ u : Fin 2 → Ω → ℝ,
      (∀ i : Fin 2, Measurable (u i) ∧ Integrable (u i) P ∧
        (∀ᵐ s ∂P, Tendsto (fun n : ℕ =>
          B 0 (n • finiteEdgeStep i) s / (n : ℝ)) atTop (𝓝 (u i s))) ∧
        (∫ s, u i s ∂P) = ∫ s, B 0 (finiteEdgeStep i) s ∂P ∧
        Tendsto (fun n : ℕ => ∫ s,
          |B 0 (n • finiteEdgeStep i) s / (n : ℝ) - u i s| ∂P)
          atTop (𝓝 0)) ∧
      ∀ (i : Fin 2) (z : Lattice) (s : Ω),
        u i (T z s) = u i s := by
  classical
  have hEach (i : Fin 2) : ∃ u : Ω → ℝ,
      (Measurable u ∧ Integrable u P ∧
        (∀ᵐ s ∂P, Tendsto (fun n : ℕ => B 0 (n • finiteEdgeStep i) s / (n : ℝ))
          atTop (𝓝 (u s))) ∧
        (∫ s, u s ∂P) = ∫ s, B 0 (finiteEdgeStep i) s ∂P ∧
        Tendsto (fun n : ℕ => ∫ s,
          |B 0 (n • finiteEdgeStep i) s / (n : ℝ) - u s| ∂P) atTop (𝓝 0)) ∧
      (∀ (z : Lattice) (s : Ω), u (T z s) = u s) := by
    obtain ⟨v, hvm, hvi, hvc, hvmean, hvL1, hvinv⟩ :=
      exists_directional_drift_ae P T hzero hadd hShift B hB hInt (finiteEdgeStep i)
    obtain ⟨u, hum, hueq, huinv⟩ :=
      exact_invariant_version P T hzero hadd hShift v hvm hvinv
    have huInt : Integrable u P := hvi.congr hueq.symm
    have huConv : ∀ᵐ s ∂P, Tendsto (fun n : ℕ =>
        B 0 (n • finiteEdgeStep i) s / (n : ℝ)) atTop (𝓝 (u s)) := by
      filter_upwards [hvc, hueq] with s hs heq
      rwa [heq]
    have huMean : (∫ s, u s ∂P) = ∫ s, B 0 (finiteEdgeStep i) s ∂P :=
      (integral_congr_ae hueq).trans hvmean
    have hIntegral (n : ℕ) :
        (∫ s, |B 0 (n • finiteEdgeStep i) s / (n : ℝ) - u s| ∂P) =
          ∫ s, |B 0 (n • finiteEdgeStep i) s / (n : ℝ) - v s| ∂P := by
      apply integral_congr_ae
      filter_upwards [hueq] with s hs
      rw [hs]
    have huL1 : Tendsto (fun n : ℕ => ∫ s,
        |B 0 (n • finiteEdgeStep i) s / (n : ℝ) - u s| ∂P) atTop (𝓝 0) := by
      simpa only [hIntegral] using hvL1
    exact ⟨u, ⟨hum, huInt, huConv, huMean, huL1⟩, huinv⟩
  let u : Fin 2 → Ω → ℝ := fun i => Classical.choose (hEach i)
  have hu (i : Fin 2) :
      (Measurable (u i) ∧ Integrable (u i) P ∧
        (∀ᵐ s ∂P, Tendsto (fun n : ℕ => B 0 (n • finiteEdgeStep i) s / (n : ℝ))
          atTop (𝓝 (u i s))) ∧
        (∫ s, u i s ∂P) = ∫ s, B 0 (finiteEdgeStep i) s ∂P ∧
        Tendsto (fun n : ℕ => ∫ s,
          |B 0 (n • finiteEdgeStep i) s / (n : ℝ) - u i s| ∂P) atTop (𝓝 0)) ∧
      (∀ (z : Lattice) (s : Ω), u i (T z s) = u i s) :=
    Classical.choose_spec (hEach i)
  exact ⟨u, fun i => (hu i).1, fun i => (hu i).2⟩

end LPP.Busemann
