/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.CanonicalCocycle
public import Busemann.Process.CanonicalMean
import Busemann.Process.ProjectedLowerBound
import LPP_Foundations.Probability.FirstMoment
import Mathlib.Tactic

/-! Means of a coupled cocycle from its canonical environment projection. -/

@[expose] public section

open MeasureTheory LPPDifferentiability
open scoped ENNReal

namespace LPP.Busemann

/-- The origin recovery and upper means identify both coupled edge means at
all signed sites, as in JR1810.03580v3, proof of Theorem 4.8 after (4.20)-(4.21). -/
theorem coupled_cocycle_edge_means
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) (h : SupportTilt g)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z, P.map (processShift z) = P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P)
    (hRecover : ∀ᵐ s ∂P,
      min (B 0 ((1 : ℤ), (0 : ℤ)) s) (B 0 ((0 : ℤ), (1 : ℤ)) s) =
        (processEnvironment s) 0)
    (hUpper₁ : (∫ s, B 0 ((1 : ℤ), (0 : ℤ)) s ∂P) ≤ -h.val.1)
    (hUpper₂ : (∫ s, B 0 ((0 : ℤ), (1 : ℤ)) s ∂P) ≤ -h.val.2) :
    ∀ x : Lattice,
      (∫ s, B x (x + ((1 : ℤ), (0 : ℤ))) s ∂P) = -h.val.1 ∧
      (∫ s, B x (x + ((0 : ℤ), (1 : ℤ))) s ∂P) = -h.val.2 := by
  classical
  -- Native absolute moments imply integrability of the actual site weight.
  obtain ⟨p, hp, hpMoment⟩ := hmoment
  have hAbs : Integrable (fun t : ℝ => |t|) μ :=
    integrable_of_nonneg_rpow_lintegral_lt_top μ (fun t => |t|)
      continuous_abs (fun t => abs_nonneg t) p (by linarith) hpMoment
  have hμ : Integrable (fun t : ℝ => t) μ := by
    apply (integrable_norm_iff (measurable_id.aestronglyMeasurable)).mp
    simpa only [Real.norm_eq_abs, id_eq] using hAbs
  have hmoment' : ∃ q : ℝ, 2 < q ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ q) ∂μ) < ∞ :=
    ⟨p, hp, hpMoment⟩

  -- Project the actual coupled cocycle given the actual environment sigma algebra.
  obtain ⟨b, hbCocycle, hbInt, hbRep, hbMean⟩ :=
    exists_canonical_condExp_cocycle μ P hMarginal hShift B hB hInt
  have hbMeas (x y : Lattice) : Measurable (b x y) := by
    have hmap : Measurable (fun ω : Environment => ((x, y), ω)) :=
      measurable_const.prodMk measurable_id
    exact hbCocycle.1.comp hmap
  have hlower₁ : ∀ᵐ s ∂P,
      (processEnvironment s) 0 ≤ B 0 ((1 : ℤ), (0 : ℤ)) s := by
    filter_upwards [hRecover] with s hs
    rw [← hs]
    exact min_le_left _ _
  have hlower₂ : ∀ᵐ s ∂P,
      (processEnvironment s) 0 ≤ B 0 ((0 : ℤ), (1 : ℤ)) s := by
    filter_upwards [hRecover] with s hs
    rw [← hs]
    exact min_le_right _ _
  have hbLower₁ : ∀ᵐ ω ∂environmentLaw μ,
      ω 0 ≤ b 0 ((1 : ℤ), (0 : ℤ)) ω :=
    ae_environment_eval_le_of_condExp μ hμ P hMarginal 0 _
      (hInt 0 ((1 : ℤ), (0 : ℤ))) hlower₁ _
      (hbMeas 0 ((1 : ℤ), (0 : ℤ))) (hbRep 0 ((1 : ℤ), (0 : ℤ)))
  have hbLower₂ : ∀ᵐ ω ∂environmentLaw μ,
      ω 0 ≤ b 0 ((0 : ℤ), (1 : ℤ)) ω :=
    ae_environment_eval_le_of_condExp μ hμ P hMarginal 0 _
      (hInt 0 ((0 : ℤ), (1 : ℤ))) hlower₂ _
      (hbMeas 0 ((0 : ℤ), (1 : ℤ))) (hbRep 0 ((0 : ℤ), (1 : ℤ)))
  have hbUpper₁ : (∫ ω, b 0 ((1 : ℤ), (0 : ℤ)) ω ∂environmentLaw μ) ≤ -h.val.1 := by
    rw [hbMean 0 ((1 : ℤ), (0 : ℤ))]
    exact hUpper₁
  have hbUpper₂ : (∫ ω, b 0 ((0 : ℤ), (1 : ℤ)) ω ∂environmentLaw μ) ≤ -h.val.2 := by
    rw [hbMean 0 ((0 : ℤ), (1 : ℤ))]
    exact hUpper₂
  have hbL1 : has_integrable_origin_edges (environmentLaw μ) b :=
    ⟨hbInt 0 ((1 : ℤ), (0 : ℤ)), hbInt 0 ((0 : ℤ), (1 : ℤ))⟩
  have hcanonical := integral_origin_edges_eq_neg_support_tilt μ hmoment' g hg h b
    hbCocycle hbL1 hbLower₁ hbLower₂ hbUpper₁ hbUpper₂
  have horigin₁ : (∫ s, B 0 ((1 : ℤ), (0 : ℤ)) s ∂P) = -h.val.1 := by
    rw [← hbMean 0 ((1 : ℤ), (0 : ℤ))]
    exact hcanonical.1
  have horigin₂ : (∫ s, B 0 ((0 : ℤ), (1 : ℤ)) s ∂P) = -h.val.2 := by
    rw [← hbMean 0 ((0 : ℤ), (1 : ℤ))]
    exact hcanonical.2

  -- The actual covariance and invariant law transport each origin mean to every site.
  have htranslate (x e : Lattice) :
      (∫ s, B x (x + e) s ∂P) = ∫ s, B 0 e s ∂P := by
    have hcov : (fun s => B x (x + e) s) =ᵐ[P]
        (fun s => B 0 e (processShift x s)) := by
      filter_upwards [hB.2.1 0 e x] with s hs
      simpa only [zero_add, add_zero, add_comm] using hs
    calc
      _ = ∫ s, B 0 e (processShift x s) ∂P := integral_congr_ae hcov
      _ = ∫ s, B 0 e s ∂P := by
        have hm : AEStronglyMeasurable (B 0 e) (P.map (processShift x)) := by
          rw [hShift x]
          exact (hInt 0 e).aestronglyMeasurable
        have heq := integral_map (measurable_processShift x).aemeasurable hm
        rw [hShift x] at heq
        exact heq.symm
  intro x
  exact ⟨(htranslate x ((1 : ℤ), (0 : ℤ))).trans horigin₁,
    (htranslate x ((0 : ℤ), (1 : ℤ))).trans horigin₂⟩

end LPP.Busemann
