/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.FiniteBusemannSharedHorizonLaw
public import Busemann.Frozen.Definitions.FiniteBusemannArrayAtSharedHorizon
public import Busemann.Frozen.Definitions.ProcessShift
public import LPP_Foundations.Probability.EnvironmentLaw
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Busemann.Finite.Translations
import Busemann.Finite.Measurability
import Busemann.Process.ShiftTopology
import ProbabilityBasics.Analysis.SignedWindowSum
import ProbabilityBasics.Probability.UniformIncrementShift
import Mathlib.Tactic

/-! The finite shared-horizon law changes by a bounded window error under a
lattice shift, as in JR1810.03580v3, proof of Theorem 4.8, (4.12).
Signed horizons are retained throughout the comparison. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology BoundedContinuousFunction

namespace LPP.Busemann

/-- The literal shared-horizon joint law has stationarity error bounded by its
two signed window boundaries; see JR1810.03580v3, proof of Theorem 4.8, (4.12).
No moment or supporting-tilt assumption is needed for this bounded-test bound. -/
private theorem norm_integral_finiteBusemann_processShift_sub_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : ℕ → ℝ × ℝ)
    (z : Lattice) (n : ℕ) (F : ProcessSample →ᵇ ℝ) :
    let ν : ProbabilityMeasure ProcessSample :=
      (show ProbabilityMeasure (Environment × Fin (n + 1)) from
        ⟨finiteBusemannSharedHorizonLaw μ n, by
          change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
          infer_instance⟩).map
        (fun p => (p.1, finiteBusemannArrayAtSharedHorizon n h p))
    ‖(∫ s, F (processShift z s) ∂(ν : Measure ProcessSample)) -
      (∫ s, F s ∂(ν : Measure ProcessSample))‖ ≤
      2 * ‖F‖ * ((z.1 + z.2).natAbs : ℝ) / (n + 1 : ℝ) := by
  classical
  let m : ℤ := z.1 + z.2
  let S : ℤ → Environment → ProcessSample := fun k ω =>
    (ω, fun j x i => finiteBusemannEdge ω (h j) x k i)
  have hS (k : ℤ) : Measurable (S k) := by
    apply measurable_id.prodMk
    apply measurable_pi_iff.mpr
    intro j
    apply measurable_pi_iff.mpr
    intro x
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_finiteBusemannEdge (h j) x k i
  have hcov (k : ℤ) (ω : Environment) :
      processShift z (S k ω) = S (k - m) (environmentTranslationEquiv z ω) := by
    apply Prod.ext
    · rfl
    · funext j x i
      change finiteBusemannEdge ω (h j) (z + x) k i =
        finiteBusemannEdge (environmentTranslationEquiv z ω) (h j) x (k - m) i
      rw [finiteBusemannEdge_translate]
      congr 1
      dsimp only [m]
      omega
  let J : Environment × Fin (n + 1) → ProcessSample := fun p =>
    (p.1, finiteBusemannArrayAtSharedHorizon n h p)
  have hJ : Measurable J :=
    measurable_fst.prodMk (measurable_finiteBusemannArrayAtSharedHorizon n h)
  let q : ProbabilityMeasure (Environment × Fin (n + 1)) :=
    ⟨finiteBusemannSharedHorizonLaw μ n, by
      change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
      infer_instance⟩
  let ν : ProbabilityMeasure ProcessSample := q.map J
  change ‖(∫ s, F (processShift z s) ∂(ν : Measure ProcessSample)) -
    (∫ s, F s ∂(ν : Measure ProcessSample))‖ ≤ _
  have hFi (k : ℤ) : Integrable (fun ω => F (S k ω)) (environmentLaw μ) := by
    apply (integrable_const ‖F‖).mono'
      (F.continuous.measurable.comp (hS k)).aestronglyMeasurable
    exact ae_of_all _ (fun ω => F.norm_coe_le_norm (S k ω))
  let a : ℤ → ℝ := fun k => ∫ ω, F (S k ω) ∂environmentLaw μ
  have ha (k : ℤ) : ‖a k‖ ≤ ‖F‖ := by
    dsimp only [a]
    rw [← integral_map (hS k).aemeasurable F.continuous.measurable.aestronglyMeasurable]
    exact F.norm_integral_le_norm _
  have htrans (k : ℤ) :
      (∫ ω, F (processShift z (S k ω)) ∂environmentLaw μ) = a (k - m) := by
    simp_rw [hcov]
    exact (measurePreserving_environmentTranslationEquiv μ z).integral_comp'
      (fun ω => F (S (k - m) ω))
  have hshiftFi (k : ℤ) : Integrable (fun ω => F (processShift z (S k ω)))
      (environmentLaw μ) := by
    apply (integrable_const ‖F‖).mono'
      (F.continuous.measurable.comp ((measurable_processShift z).comp (hS k))).aestronglyMeasurable
    exact ae_of_all _ (fun ω => F.norm_coe_le_norm (processShift z (S k ω)))
  have havg (G : ProcessSample → ℝ) (hG : Measurable G)
      (hi : ∀ k : ℤ, Integrable (fun ω => G (S k ω)) (environmentLaw μ)) :
      (∫ s, G s ∂(ν : Measure ProcessSample)) =
        (∑ u : Fin (n + 1), ∫ ω, G (S ((u.val + 1 : ℕ) : ℤ) ω)
          ∂environmentLaw μ) / (n + 1 : ℝ) := by
    change (∫ s, G s ∂Measure.map J (finiteBusemannSharedHorizonLaw μ n)) = _
    rw [integral_map hJ.aemeasurable hG.aestronglyMeasurable]
    change (∫ p : Environment × Fin (n + 1),
      G (S ((p.2.val + 1 : ℕ) : ℤ) p.1) ∂uniformOriginProduct (environmentLaw μ) n) = _
    exact integral_uniformOrigin_family (environmentLaw μ) n
      (fun u ω => G (S ((u.val + 1 : ℕ) : ℤ) ω))
      (fun u => hG.comp (hS _)) (fun u => hi _)
  rw [havg (fun s => F (processShift z s))
      (F.continuous.measurable.comp (measurable_processShift z)) hshiftFi,
    havg F F.continuous.measurable hFi, ← sub_div]
  simp_rw [htrans]
  change ‖((∑ u : Fin (n + 1), a (((u.val + 1 : ℕ) : ℤ) - m)) -
    (∑ u : Fin (n + 1), a ((u.val + 1 : ℕ) : ℤ))) / (n + 1 : ℝ)‖ ≤ _
  rw [norm_div, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hb := ProbabilityBasics.norm_sum_int_shift_sub_le (fun k : ℤ => a (k + 1))
    ‖F‖ (fun k => ha (k + 1)) (-m) (n + 1)
  simpa only [Int.natAbs_neg, Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
    add_left_comm, sub_eq_add_neg] using hb

/-- Every weak limit of the literal shared-horizon joint laws is invariant under
lattice translation, as in JR1810.03580v3, proof of Theorem 4.8 after (4.17).
The finite signed-window comparison is proved internally without moment assumptions. -/
theorem measurePreserving_processShift_of_finiteBusemann_weak_limit
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : ℕ → ℝ × ℝ)
    (P : ProbabilityMeasure ProcessSample) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hweak :
      let ν : ℕ → ProbabilityMeasure ProcessSample := fun n =>
        (show ProbabilityMeasure (Environment × Fin (n + 1)) from
          ⟨finiteBusemannSharedHorizonLaw μ n, by
            change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
            infer_instance⟩).map
          (fun p => (p.1, finiteBusemannArrayAtSharedHorizon n h p))
      Tendsto (ν ∘ φ) atTop (𝓝 P)) (z : Lattice) :
    MeasurePreserving (processShift z) (P : Measure ProcessSample)
      (P : Measure ProcessSample) := by
  let ν : ℕ → ProbabilityMeasure ProcessSample := fun n =>
    (show ProbabilityMeasure (Environment × Fin (n + 1)) from
      ⟨finiteBusemannSharedHorizonLaw μ n, by
        change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
        infer_instance⟩).map
      (fun p => (p.1, finiteBusemannArrayAtSharedHorizon n h p))
  change Tendsto (ν ∘ φ) atTop (𝓝 P) at hweak
  have hmapped := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (ν ∘ φ) P hweak (continuous_processShift z)
  refine ⟨measurable_processShift z, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  have hl := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmapped F).sub
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak F)
  have hz : Tendsto
      (fun k => (∫ s, F (processShift z s) ∂(ν (φ k) : Measure ProcessSample)) -
        (∫ s, F s ∂(ν (φ k) : Measure ProcessSample))) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k =>
      norm_integral_finiteBusemann_processShift_sub_le μ h z (φ k) F)
    have hd : Tendsto
        (fun n : ℕ => 2 * ‖F‖ * ((z.1 + z.2).natAbs : ℝ) / (n + 1 : ℝ))
        atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_add_atTop_iff_nat 1).2
          (tendsto_const_div_atTop_nhds_zero_nat
            (2 * ‖F‖ * ((z.1 + z.2).natAbs : ℝ)))
    exact hd.comp hφ.tendsto_atTop
  have htest (k : ℕ) :
      (∫ s, F s ∂(((ν ∘ φ) k).map (processShift z) : Measure ProcessSample)) =
        ∫ s, F (processShift z s) ∂(ν (φ k) : Measure ProcessSample) := by
    change (∫ s, F s ∂(ν (φ k) : Measure ProcessSample).map (processShift z)) = _
    exact integral_map (measurable_processShift z).aemeasurable
      F.continuous.measurable.aestronglyMeasurable
  have hl' : Tendsto
      (fun k => (∫ s, F (processShift z s) ∂(ν (φ k) : Measure ProcessSample)) -
        (∫ s, F s ∂(ν (φ k) : Measure ProcessSample))) atTop
      (𝓝 ((∫ s, F s ∂(P : Measure ProcessSample).map (processShift z)) -
        (∫ s, F s ∂(P : Measure ProcessSample)))) := by
    convert hl using 1
    · funext k
      exact congrArg (fun r : ℝ => r -
        (∫ s, F s ∂(ν (φ k) : Measure ProcessSample))) (htest k).symm
    · simp only [ProbabilityMeasure.toMeasure_map]
  exact sub_eq_zero.mp (tendsto_nhds_unique hl' hz)

end LPP.Busemann
