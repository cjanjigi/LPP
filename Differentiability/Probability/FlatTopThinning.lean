/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Analysis.ToQuadrant
public import Differentiability.Model.OrientedPercolation
public import LPP_Foundations.Model.LastPassage.Basic
public import LPP_Foundations.Model.LastPassage.Bounds
public import Martin2004.Analysis.RationalPassageNormalization
public import LPP_Foundations.Probability.EnvironmentMap
public import LPP_Foundations.Probability.EnvironmentResample
public import LPP_Foundations.Probability.PassageMeasurable
public import ProbabilityBasics.Probability.PositiveMomentTail
public import Differentiability.Probability.TopIndicatorShape
public import Martin2004.Probability.WeakNegativeShape
public import LPP_Foundations.Shape.Uniqueness

/-!
# A top shape equal to one forces the shape of the weights to equal one

If the shape of the 0/1 top field is one in a direction, so is the shape of the weights. With `m`
the mean of the weight law off the top, a best path chosen from the top field alone has expected
weight `m * length + (1 - m) * (expected top count)`; divide by the length.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

local notation "len" d:max => ((d.1 + d.2 : ℕ) : ℝ)

private noncomputable def topInd (x : ℝ) : ℝ := if x = 1 then 1 else 0

private theorem measurable_topInd : Measurable topInd :=
  Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const measurable_const

private theorem topInd_bounds (x : ℝ) : 0 ≤ 1 - topInd x ∧ 1 - topInd x ≤ 1 := by
  unfold topInd; split_ifs <;> norm_num

private theorem topField_eq (ω : Environment) : topField ω = fun z => topInd (ω z) := by
  rfl

private theorem measurable_topField : Measurable topField := by
  have e : topField = fun ω z => topInd (ω z) := funext topField_eq
  rw [e]; exact measurable_coordinatewise_environment_map topInd measurable_topInd

private theorem topField_mem (ω : Environment) (z : Lattice) :
    0 ≤ topField ω z ∧ topField ω z ≤ 1 := by
  rw [congrFun (topField_eq ω) z]; unfold topInd; split_ifs <;> norm_num

private theorem eq_centered_add (m x : ℝ) :
    x = (x - m) * (1 - topInd x) + m + (1 - m) * topInd x := by
  unfold topInd; split_ifs with h
  · subst h; ring
  · ring

-- `m` is the off-top mean: the centered off-top part is integrable with mean zero.
private theorem exists_centering (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun x : ℝ => x) ν) (hp₁ : ν {1} < 1) :
    ∃ m : ℝ, Integrable (fun x : ℝ => (x - m) * (1 - topInd x)) ν ∧
      ∫ x, (x - m) * (1 - topInd x) ∂ν = 0 := by
  have hti : topInd = Set.indicator ({1} : Set ℝ) (fun _ => (1 : ℝ)) := by
    funext x; by_cases h : x = 1 <;> simp [topInd, h]
  have hI : Integrable topInd ν := by
    rw [hti]; exact (integrable_const (1 : ℝ)).indicator (measurableSet_singleton _)
  have hc : Integrable (fun x : ℝ => 1 - topInd x) ν := (integrable_const (1 : ℝ)).sub hI
  have hxc : Integrable (fun x : ℝ => x * (1 - topInd x)) ν := by
    refine hint.norm.mono'
      (measurable_id.mul (measurable_const.sub measurable_topInd)).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    show ‖x * (1 - topInd x)‖ ≤ ‖x‖
    rw [norm_mul, Real.norm_eq_abs (1 - topInd x), abs_of_nonneg (topInd_bounds x).1]
    exact (mul_le_mul_of_nonneg_left (topInd_bounds x).2 (norm_nonneg _)).trans_eq (mul_one _)
  have hlt : ν.real {1} < 1 := by
    simpa [Measure.real] using
      (ENNReal.toReal_lt_toReal (measure_ne_top ν {1}) ENNReal.one_ne_top).2 hp₁
  have hden : ∫ x, (1 - topInd x) ∂ν = 1 - ν.real {1} := by
    rw [integral_sub (integrable_const (1 : ℝ)) hI, hti,
      integral_indicator_const _ (measurableSet_singleton (1 : ℝ))]
    simp
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (∫ x, x * (1 - topInd x) ∂ν) / (1 - ν.real {1}) := ⟨_, rfl⟩
  have hmul : m * (1 - ν.real {1}) = ∫ x, x * (1 - topInd x) ∂ν := by
    have hne : (1 - ν.real {1}) ≠ 0 := ne_of_gt (by linarith)
    rw [hm]; field_simp
  have hsplit : (fun x : ℝ => (x - m) * (1 - topInd x)) =
      fun x => x * (1 - topInd x) - m * (1 - topInd x) := by funext x; ring
  refine ⟨m, ?_, ?_⟩
  · rw [hsplit]; exact hxc.sub (hc.const_mul m)
  · rw [hsplit, integral_sub hxc (hc.const_mul m), integral_const_mul, hden, hmul]; ring

-- The centered off-top weight at a site is uncorrelated with bounded functions of the top field.
private theorem centered_term (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℝ)
    (hD : Integrable (fun x : ℝ => (x - m) * (1 - topInd x)) ν)
    (hm : ∫ x, (x - m) * (1 - topInd x) ∂ν = 0) (F : Environment → ℝ) (hF : Measurable F)
    (hF1 : ∀ τ, |F τ| ≤ 1) (v : Lattice) :
    Integrable (fun ω : Environment => F (topField ω) * ((ω v - m) * (1 - topInd (ω v))))
      (environmentLaw ν) ∧
    ∫ ω, F (topField ω) * ((ω v - m) * (1 - topInd (ω v))) ∂environmentLaw ν = 0 := by
  have hev : Measurable (fun ω : Environment => ω v) := measurable_environment_eval v
  have hmeas : Measurable (fun ω : Environment =>
      F (topField ω) * ((ω v - m) * (1 - topInd (ω v)))) :=
    (hF.comp measurable_topField).mul
      ((hev.sub_const m).mul (measurable_const.sub (measurable_topInd.comp hev)))
  refine ⟨?_, ?_⟩
  · have h : Integrable (fun x : ℝ => (x - m) * (1 - topInd x))
        ((environmentLaw ν).map (fun ω : Environment => ω v)) := by
      rw [environmentLaw_map_eval]; exact hD
    refine (h.comp_measurable hev).norm.mono' hmeas.aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    show ‖F (topField ω) * ((ω v - m) * (1 - topInd (ω v)))‖ ≤
      ‖(ω v - m) * (1 - topInd (ω v))‖
    rw [norm_mul (F (topField ω))]
    exact (mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hF1 _)
      (norm_nonneg _)).trans_eq (one_mul _)
  · have htopupd : ∀ (ω' : Environment) (x : ℝ),
        topField (Function.update ω' v x) = Function.update (topField ω') v (topInd x) := by
      intro ω' x
      funext z
      by_cases hz : z = v <;> simp [topField_eq, hz]
    have hpt : ∀ p : ℝ × Environment,
        F (topField (Function.update p.2 v p.1)) *
            ((Function.update p.2 v p.1 v - m) * (1 - topInd (Function.update p.2 v p.1 v))) =
          ((p.1 - m) * (1 - topInd p.1)) * F (Function.update (topField p.2) v 0) := by
      intro p
      rw [htopupd, Function.update_self]
      by_cases hx : p.1 = 1
      · have h1 : topInd p.1 = 1 := by simp [topInd, hx]
        rw [h1]; simp
      · have h0 : topInd p.1 = 0 := by simp [topInd, hx]
        rw [h0]; ring
    rw [← integral_environment_update ν v _ hmeas, integral_congr_ae (ae_of_all _ hpt),
      integral_prod_mul (fun x : ℝ => (x - m) * (1 - topInd x))
        (fun ω : Environment => F (Function.update (topField ω) v 0)), hm, zero_mul]

-- Weight of a path: centered off-top part plus the conditional-mean value of its top count.
private theorem pathWeight_decomp (m : ℝ) {d : ℕ × ℕ} (ω : Environment)
    (p : Path (0 : Lattice) d) :
    pathWeight ω p = (∑ i : Fin (d.1 + d.2), (ω (p.vertex i.castSucc) - m) *
          (1 - topInd (ω (p.vertex i.castSucc)))) +
      (m * len d + (1 - m) * pathWeight (topField ω) p) := by
  have hT : pathWeight (topField ω) p =
      ∑ i : Fin (d.1 + d.2), topInd (ω (p.vertex i.castSucc)) := by
    unfold pathWeight; rw [topField_eq]
  have h1 : pathWeight ω p = ∑ i : Fin (d.1 + d.2),
      ((ω (p.vertex i.castSucc) - m) * (1 - topInd (ω (p.vertex i.castSucc))) + m +
        (1 - m) * topInd (ω (p.vertex i.castSucc))) := by
    unfold pathWeight; exact Finset.sum_congr rfl fun i _ => eq_centered_add m _
  rw [h1, hT]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  ring

-- Indicators of the events "this path is the first maximizer of the top count".
private theorem exists_selector (d : ℕ × ℕ) :
    ∃ F : Path (0 : Lattice) d → Environment → ℝ,
      (∀ p, Measurable (F p)) ∧ (∀ p τ, 0 ≤ F p τ ∧ F p τ ≤ 1) ∧
      (∀ τ, ∑ p, F p τ = 1) ∧
      (∀ p τ, F p τ ≠ 0 → pathWeight τ p = lastPassage τ 0 d) := by
  classical
  obtain ⟨e⟩ : Nonempty (Path (0 : Lattice) d ≃ Fin (Fintype.card (Path (0 : Lattice) d))) :=
    ⟨Fintype.equivFin _⟩
  obtain ⟨C, hCdef⟩ : ∃ C : Path (0 : Lattice) d → Environment → Prop,
      ∀ p τ, C p τ ↔ (pathWeight τ p = lastPassage τ 0 d ∧
        ∀ q, e q < e p → ¬ pathWeight τ q = lastPassage τ 0 d) :=
    ⟨fun p τ => pathWeight τ p = lastPassage τ 0 d ∧
      ∀ q, e q < e p → ¬ pathWeight τ q = lastPassage τ 0 d, fun _ _ => Iff.rfl⟩
  have hex : ∀ τ : Environment, ∃ p, C p τ := by
    intro τ
    obtain ⟨p0, hp0⟩ := exists_pathWeight_eq_lastPassage τ 0 d
    obtain ⟨p, hpS, hmin⟩ := Finset.exists_min_image
      (Finset.univ.filter fun p : Path (0 : Lattice) d => pathWeight τ p = lastPassage τ 0 d) e
      ⟨p0, by simp [hp0]⟩
    refine ⟨p, (hCdef p τ).2 ⟨(Finset.mem_filter.1 hpS).2, fun q hq hqm => ?_⟩⟩
    exact absurd (hmin q (Finset.mem_filter.2 ⟨Finset.mem_univ q, hqm⟩)) (not_le.2 hq)
  have huniq : ∀ τ p q, C p τ → C q τ → p = q := by
    intro τ p q hp hq
    have hp' := (hCdef _ _).1 hp
    have hq' := (hCdef _ _).1 hq
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (e.injective h) : e p ≠ e q) with h | h
    · exact hq'.2 p h hp'.1
    · exact hp'.2 q h hq'.1
  refine ⟨fun p τ => if C p τ then 1 else 0, ?_, fun p τ => ?_, ?_, ?_⟩
  · intro p
    have hC : Measurable (fun τ : Environment => C p τ) := by
      have h : Measurable (fun τ : Environment => pathWeight τ p = lastPassage τ 0 d ∧
          ∀ q, e q < e p → ¬ pathWeight τ q = lastPassage τ 0 d) :=
        ((measurable_pathWeight p).eq (measurable_lastPassage 0 d)).and
          (Measurable.forall fun q => measurable_const.imp
            (((measurable_pathWeight q).eq (measurable_lastPassage 0 d)).not))
      simp only [hCdef]; exact h
    exact Measurable.ite (measurableSet_setOfPred.2 hC) measurable_const measurable_const
  · show 0 ≤ (if C p τ then (1 : ℝ) else 0) ∧ (if C p τ then (1 : ℝ) else 0) ≤ 1
    split_ifs <;> norm_num
  · intro τ
    obtain ⟨p0, hp0⟩ := hex τ
    rw [Finset.sum_eq_single p0]
    · simp [hp0]
    · intro q _ hq
      have hcq : ¬ C q τ := fun h => hq (huniq τ q p0 h hp0)
      simp [hcq]
    · intro h; exact absurd (Finset.mem_univ p0) h
  · intro p τ h
    by_cases hc : C p τ
    · exact ((hCdef p τ).1 hc).1
    · exact absurd (by simp [hc]) (show (if C p τ then (1 : ℝ) else 0) ≠ 0 from h)

-- Expected last-passage time versus the conditional-mean value of a top-field best path.
private theorem lastPassage_mean_lower (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℝ)
    (hD : Integrable (fun x : ℝ => (x - m) * (1 - topInd x)) ν)
    (hm : ∫ x, (x - m) * (1 - topInd x) ∂ν = 0) (d : ℕ × ℕ)
    (hL : Integrable (fun ω : Environment => lastPassage ω 0 d) (environmentLaw ν)) :
    m * len d + (1 - m) * ∫ ω, lastPassage (topField ω) 0 d ∂environmentLaw ν ≤
      ∫ ω, lastPassage ω 0 d ∂environmentLaw ν := by
  obtain ⟨F, hFm, hF01, hFsum, hFmax⟩ := exists_selector d
  have hF1 : ∀ p τ, |F p τ| ≤ 1 := fun p τ =>
    abs_le.2 ⟨by linarith [(hF01 p τ).1], (hF01 p τ).2⟩
  have ct := fun (p : Path (0 : Lattice) d) (i : Fin (d.1 + d.2)) =>
    centered_term ν m hD hm (F p) (hFm p) (hF1 p) (p.vertex i.castSucc)
  have hH : ∀ ω : Environment, ∑ p, F p (topField ω) * pathWeight ω p =
      (m * len d + (1 - m) * lastPassage (topField ω) 0 d) +
        ∑ p, ∑ i : Fin (d.1 + d.2), F p (topField ω) * ((ω (p.vertex i.castSucc) - m) *
          (1 - topInd (ω (p.vertex i.castSucc)))) := by
    intro ω
    have h1 : ∀ p : Path (0 : Lattice) d, F p (topField ω) * pathWeight ω p =
        F p (topField ω) * (m * len d + (1 - m) * lastPassage (topField ω) 0 d) +
          ∑ i : Fin (d.1 + d.2), F p (topField ω) * ((ω (p.vertex i.castSucc) - m) *
            (1 - topInd (ω (p.vertex i.castSucc)))) := by
      intro p
      by_cases h0 : F p (topField ω) = 0
      · simp [h0]
      · rw [pathWeight_decomp m ω p, hFmax p _ h0]
        simp only [mul_add, Finset.mul_sum]
        ring
    simp only [h1]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hFsum, one_mul]
  have hW : ∀ ω : Environment, ∑ p, F p (topField ω) * pathWeight ω p ≤ lastPassage ω 0 d :=
    fun ω => (Finset.sum_le_sum fun p _ =>
      mul_le_mul_of_nonneg_left (pathWeight_le_lastPassage ω p) (hF01 p _).1).trans_eq
        (by rw [← Finset.sum_mul, hFsum, one_mul])
  have hLtop : Integrable (fun ω : Environment => lastPassage (topField ω) 0 d)
      (environmentLaw ν) := by
    refine (integrable_const (len d)).mono'
      ((measurable_lastPassage 0 d).comp measurable_topField).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    have h0 := const_le_lastPassage (topField ω) 0 d 0 (fun z => (topField_mem ω z).1)
    have h1 := lastPassage_le_const (topField ω) 0 d 1 (fun z => (topField_mem ω z).2)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by simpa using h0 : (0 : ℝ) ≤ lastPassage (topField ω) 0 d)]
    simpa using h1
  have hA : Integrable (fun ω : Environment =>
      m * len d + (1 - m) * lastPassage (topField ω) 0 d) (environmentLaw ν) :=
    (integrable_const _).add (hLtop.const_mul _)
  have hS : Integrable (fun ω : Environment => ∑ p, ∑ i : Fin (d.1 + d.2),
      F p (topField ω) * ((ω (p.vertex i.castSucc) - m) *
        (1 - topInd (ω (p.vertex i.castSucc))))) (environmentLaw ν) :=
    integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun i _ => (ct p i).1
  have hSint : ∫ ω, ∑ p, ∑ i : Fin (d.1 + d.2), F p (topField ω) *
      ((ω (p.vertex i.castSucc) - m) * (1 - topInd (ω (p.vertex i.castSucc))))
        ∂environmentLaw ν = 0 := by
    rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun i _ => (ct p i).1]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [integral_finsetSum _ fun i _ => (ct p i).1]
    exact Finset.sum_eq_zero fun i _ => (ct p i).2
  have hfun := funext hH
  have hWint : Integrable (fun ω : Environment => ∑ p, F p (topField ω) * pathWeight ω p)
      (environmentLaw ν) := by rw [hfun]; exact hA.add hS
  have hEq : ∫ ω, (m * len d + (1 - m) * lastPassage (topField ω) 0 d) ∂environmentLaw ν =
      m * len d + (1 - m) * ∫ ω, lastPassage (topField ω) 0 d ∂environmentLaw ν := by
    rw [integral_add (integrable_const _) (hLtop.const_mul _), integral_const,
      integral_const_mul]
    simp
  calc m * len d + (1 - m) * ∫ ω, lastPassage (topField ω) 0 d ∂environmentLaw ν
      = ∫ ω, (m * len d + (1 - m) * lastPassage (topField ω) 0 d) ∂environmentLaw ν :=
        hEq.symm
    _ = ∫ ω, ∑ p, F p (topField ω) * pathWeight ω p ∂environmentLaw ν := by
        rw [hfun, integral_add hA hS, hSint, add_zero]
    _ ≤ ∫ ω, lastPassage ω 0 d ∂environmentLaw ν := integral_mono hWint hL hW

private theorem ae_environment_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ t ∂ν, t ≤ 1) : ∀ᵐ ω ∂environmentLaw ν, ∀ z : Lattice, ω z ≤ 1 :=
  ae_all_iff.2 fun z => ae_of_ae_map (p := fun y : ℝ => y ≤ 1)
    (measurable_environment_eval z).aemeasurable (by rw [environmentLaw_map_eval]; exact hle)

private theorem limit_eq_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hae : ∀ᵐ ω ∂environmentLaw ν, ∀ z : Lattice, ω z ≤ 1) (m : ℝ)
    (hD : Integrable (fun x : ℝ => (x - m) * (1 - topInd x)) ν)
    (hm : ∫ x, (x - m) * (1 - topInd x) ∂ν = 0) (D : ℕ → ℕ × ℕ) (G : ℝ)
    (hlen : Tendsto (fun k : ℕ => (len (D k)) / (k : ℝ)) atTop (𝓝 1))
    (hL : Tendsto (fun k : ℕ => (∫ ω, lastPassage ω 0 (D k) ∂environmentLaw ν) / (k : ℝ))
      atTop (𝓝 G))
    (hLint : ∀ d : ℕ × ℕ,
      Integrable (fun ω : Environment => lastPassage ω 0 d) (environmentLaw ν))
    (hT : Tendsto (fun k : ℕ =>
      (∫ ω, lastPassage (topField ω) 0 (D k) ∂environmentLaw ν) / (k : ℝ)) atTop (𝓝 1)) :
    G = 1 := by
  apply le_antisymm
  · refine le_of_tendsto_of_tendsto' hL hlen fun k => ?_
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg k)
    refine (integral_mono_ae (hLint _) (integrable_const (len (D k)))
      (hae.mono fun ω h => (lastPassage_le_const ω 0 _ 1 h).trans_eq (mul_one _))).trans_eq ?_
    simp
  · have hlow := (hlen.const_mul m).add (hT.const_mul (1 - m))
    rw [show m * 1 + (1 - m) * 1 = 1 by ring] at hlow
    refine le_of_tendsto_of_tendsto' hlow hL fun k => ?_
    have h := lastPassage_mean_lower ν m hD hm (D k) (hLint _)
    calc m * (len (D k) / (k : ℝ)) + (1 - m) *
          ((∫ ω, lastPassage (topField ω) 0 (D k) ∂environmentLaw ν) / (k : ℝ))
        = (m * len (D k) + (1 - m) *
          ∫ ω, lastPassage (topField ω) 0 (D k) ∂environmentLaw ν) / (k : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right h (Nat.cast_nonneg k)

/-- If the top shape equals one at a direction `(t, 1 - t)`, the shape of the weights equals one
there. -/
theorem gbar_eq_one_of_gtop_eq_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ t ∂ν, t ≤ 1) (hp₀ : 0 < ν {1}) (hp₁ : ν {1} < 1)
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂ν) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (gtop : Quadrant → ℝ) (htcont : Continuous gtop)
    (hthom : ∀ (c : ℝ≥0) (x : Quadrant), gtop (c * x.1, c * x.2) = (c : ℝ) * gtop x)
    (htconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * gtop x + (t : ℝ) * gtop y ≤ gtop (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (htshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage (topField ω) 0 d - gtop ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (h1 : gtop (toQuadrant (t, 1 - t)) = 1) :
    g (toQuadrant (t, 1 - t)) = 1 := by
  have _hunused := And.intro hp₀ (And.intro hgconc htconc)
  have hmom : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ (3 : ℝ)) ∂ν) < ∞ :=
    (lintegral_mono_ae (g := fun _ => (1 : ℝ≥0∞)) (hle.mono fun x hx => ENNReal.ofReal_le_one.2
      (Real.rpow_le_one (le_max_right x 0) (max_le hx zero_le_one) (by norm_num)))).trans_lt
        (by simp)
  have hpos := positive_integrated_sqrt_tail_lt_top_of_moment ν (p := (3 : ℝ)) (by norm_num) hmom
  have hint := integrable_id_of_negative_moment_and_positive_tail ν hneg hpos
  obtain ⟨m, hD, hm⟩ := exists_centering ν hint hp₁
  -- the shape of the weights, with its expected rate
  obtain ⟨g0, hg0, -⟩ :=
    exists_unique_shape_with_expected_rate_of_negative_moment_and_positive_tail ν hneg hpos
  have hgeq : g = g0 := shapeCandidates_eq ν g g0 hgcont hg0.1 hghom hg0.2.1
    (hgshape.mono fun ω h ε hε => by obtain ⟨N, -, hN⟩ := h ε hε; exact ⟨N, hN⟩)
    (hg0.2.2.2.1.mono fun ω h ε hε => by obtain ⟨N, -, hN⟩ := h ε hε; exact ⟨N, hN⟩)
  -- the shape of the top field, with its expected rate, through the image law
  have hν' : ∀ᵐ s ∂ν.map topInd, 0 ≤ s ∧ s ≤ 1 :=
    (ae_map_iff measurable_topInd.aemeasurable
      (measurableSet_Icc (a := (0 : ℝ)) (b := 1))).2
        (ae_of_all _ fun x => ⟨by linarith [(topInd_bounds x).2], by linarith [(topInd_bounds x).1]⟩)
  obtain ⟨g', hg'c, hg'h, -, hg'shape, hg'lim, -⟩ :=
    exists_shape_with_expected_bounds_of_ae_mem_unit_interval (ν.map topInd) hν'
  have hlaw : (environmentLaw ν).map topField = environmentLaw (ν.map topInd) := by
    have e : topField = fun ω z => topInd (ω z) := funext topField_eq
    rw [e]; exact environmentLaw_map_coordinatewise ν topInd measurable_topInd
  have hshape' : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage (topField ω) 0 d - g' ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ) := by
    have h := hg'shape
    rw [← hlaw] at h
    exact ae_of_ae_map measurable_topField.aemeasurable h
  have hgt : gtop = g' := by
    obtain ⟨ω, h1', h2'⟩ := (htshape.and hshape').exists
    exact shapeCandidates_eq_of_common_environment gtop g' htcont hg'c hthom hg'h (topField ω)
      (fun ε hε => by obtain ⟨N, -, hN⟩ := h1' ε hε; exact ⟨N, hN⟩)
      (fun ε hε => by obtain ⟨N, -, hN⟩ := h2' ε hε; exact ⟨N, hN⟩)
  have hmapint : ∀ d : ℕ × ℕ, ∫ ω, lastPassage (topField ω) 0 d ∂environmentLaw ν =
      ∫ η, lastPassage η 0 d ∂environmentLaw (ν.map topInd) := by
    intro d
    rw [← hlaw, integral_map measurable_topField.aemeasurable
      (measurable_lastPassage 0 d).aestronglyMeasurable]
  -- the direction `(t, 1 - t)` and its floor lattice points
  have hsum : (((toQuadrant (t, 1 - t)).1 : ℝ≥0) : ℝ) + ((toQuadrant (t, 1 - t)).2 : ℝ≥0) = 1 := by
    show ((t.toNNReal : ℝ≥0) : ℝ) + ((1 - t).toNNReal : ℝ≥0) = 1
    rw [Real.coe_toNNReal t ht.1, Real.coe_toNNReal _ (sub_nonneg.2 ht.2)]; ring
  have hlen := tendsto_floor_pair_length (((toQuadrant (t, 1 - t)).1 : ℝ≥0) : ℝ)
    (((toQuadrant (t, 1 - t)).2 : ℝ≥0) : ℝ) (toQuadrant (t, 1 - t)).1.property
    (toQuadrant (t, 1 - t)).2.property
  rw [hsum] at hlen
  have hLlim := hg0.2.2.2.2.1 (toQuadrant (t, 1 - t))
  have hTlim := hg'lim (toQuadrant (t, 1 - t))
  rw [← hgt, h1] at hTlim
  have hres := limit_eq_one ν (ae_environment_le_one ν hle) m hD hm
    (fun k : ℕ => (⌊(k : ℝ) * (((toQuadrant (t, 1 - t)).1 : ℝ≥0) : ℝ)⌋₊,
      ⌊(k : ℝ) * (((toQuadrant (t, 1 - t)).2 : ℝ≥0) : ℝ)⌋₊))
    (g0 (toQuadrant (t, 1 - t))) hlen hLlim hg0.2.2.2.2.2
    (Tendsto.congr (fun k => by rw [hmapint]) hTlim)
  rwa [hgeq]

end LPPDifferentiability
