/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatDensitySource.FirstSplit
import all Differentiability.FinalDraft.FlatTop.OriginEdge
import all Differentiability.FinalDraft.FlatTopRates.RightContinuity
import Differentiability.Probability.LevelIndependence
import Differentiability.Model.OrientedPercolationLaws
import LPP_Foundations.Probability.CoordinateLaw

/-! The next east site can split the two edges whenever they have not yet split. -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LPPDifferentiability.FinalDraft

/-- The point with first coordinate at the threshold edge on the given level. -/
noncomputable def thresholdEdgeSite (p : unitInterval) (n : ℕ) (u : Environment) : Lattice :=
  let a := halfLineEdge (thresholdSiteEnvironment p u) n
  (a, (n : ℤ) - a)

/-- The point identifying the edge always lies at the prescribed level. -/
theorem thresholdEdgeSite_level (p : unitInterval) (n : ℕ) (u : Environment) :
    (thresholdEdgeSite p n u).1 + (thresholdEdgeSite p n u).2 = (n : ℤ) := by
  simp only [thresholdEdgeSite]
  omega

/-- The point at the threshold edge is determined by uniforms through its own level. -/
theorem measurable_thresholdEdgeSite_levels (p : unitInterval) (n : ℕ) :
    Measurable[levelsAtMost (n : ℤ)] (thresholdEdgeSite p n) :=
  (Measurable.of_discrete (f := fun a : ℤ => ((a, (n : ℤ) - a) : Lattice))).comp
    (measurable_thresholdHalfLineEdge_levels p n)

/-- When the lower process reaches a level, its rightmost site is attained. -/
theorem thresholdEdgeSite_mem {p : unitInterval} {n : ℕ} {u : Environment}
    (hne : (openReachSet (topSites (thresholdSiteEnvironment p u)) antidiagHalfLine n).Nonempty) :
    thresholdEdgeSite p n u ∈ openReachSet
      (topSites (thresholdSiteEnvironment p u)) antidiagHalfLine n := by
  obtain ⟨v, hv, hfst⟩ := maxFirst_mem _ hne
    (bddAbove_fst_halfLineReach (thresholdSiteEnvironment p u) n)
  have hlevel : v.1 + v.2 = (n : ℤ) := by
    have h := openReachSet_subset_levelSet _ _ 0 n antidiagHalfLine_subset_levelSet hv
    simpa [levelSet] using h
  change v.1 = halfLineEdge (thresholdSiteEnvironment p u) n at hfst
  have heq : thresholdEdgeSite p n u = v := Prod.ext hfst.symm (by
    change (n : ℤ) - halfLineEdge (thresholdSiteEnvironment p u) n = v.2
    omega)
  rwa [heq]

/-- At the site directly east of the lower rightmost site, a fresh opening splits the two
edges if it is open only at the higher threshold. -/
private theorem edgeSplit_succ_of_east {p q : unitInterval} (hpq : p ≤ q) (n : ℕ)
    (u : Environment)
    (hne : ∀ k, (openReachSet (topSites (thresholdSiteEnvironment p u))
      antidiagHalfLine k).Nonempty)
    (hu : u (thresholdEdgeSite p n u + (1, 0)) ∈ Ioc (p : ℝ) (q : ℝ)) :
    u ∈ edgeSplit p q (n + 1) := by
  let t := thresholdEdgeSite p n u
  let v : Lattice := t + (1, 0)
  let O := topSites (thresholdSiteEnvironment p u)
  let O' := topSites (thresholdSiteEnvironment q u)
  have hsub : O ⊆ O' := topSites_thresholdSiteEnvironment_mono u hpq
  have htp : t ∈ openReachSet O antidiagHalfLine n := thresholdEdgeSite_mem (hne n)
  have htq := openReachSet_mono hsub (subset_rfl : antidiagHalfLine ⊆ antidiagHalfLine) n htp
  have hvq : v ∈ O' := (mem_topSites_thresholdSiteEnvironment_iff q u v).2 hu.2
  have hvp : v ∉ O := fun h => hu.1.not_ge
    ((mem_topSites_thresholdSiteEnvironment_iff p u v).1 h)
  have hv : v ∈ openReachSet O' antidiagHalfLine (n + 1) :=
    (mem_openReachSet_succ_iff O' antidiagHalfLine n v).2
      ⟨hvq, Or.inl (by simpa only [v, add_sub_cancel_right] using htq)⟩
  have hq : v.1 ≤ halfLineEdge (thresholdSiteEnvironment q u) (n + 1) :=
    le_maxFirst _ (bddAbove_fst_halfLineReach _ _) hv
  have htlevel := thresholdEdgeSite_level p n u
  obtain ⟨w, hw, hwe⟩ := maxFirst_mem _ (hne (n + 1))
    (bddAbove_fst_halfLineReach (thresholdSiteEnvironment p u) (n + 1))
  change w.1 = halfLineEdge (thresholdSiteEnvironment p u) (n + 1) at hwe
  obtain ⟨hwO, hstep⟩ := (mem_openReachSet_succ_iff O antidiagHalfLine n w).1 hw
  have hwbound : w.1 ≤ v.1 := by
    rcases hstep with hwest | hsouth
    · have hb := le_maxFirst _ (bddAbove_fst_halfLineReach (thresholdSiteEnvironment p u) n) hwest
      change w.1 - 1 ≤ t.1 at hb
      change w.1 ≤ t.1 + 1
      omega
    · have hb := le_maxFirst _ (bddAbove_fst_halfLineReach (thresholdSiteEnvironment p u) n) hsouth
      change w.1 - 0 ≤ t.1 at hb
      change w.1 ≤ t.1 + 1
      omega
  have hwlevel : w.1 + w.2 = ((n + 1 : ℕ) : ℤ) := by
    have h := openReachSet_subset_levelSet _ _ 0 (n + 1) antidiagHalfLine_subset_levelSet hw
    simpa [levelSet] using h
  have hwne : w.1 ≠ v.1 := by
    intro he
    have hwv : w = v := Prod.ext he (by
      change w.2 = t.2 + 0
      change w.1 = t.1 + 1 at he
      change t.1 + t.2 = (n : ℤ) at htlevel
      omega)
    exact hvp (hwv ▸ hwO)
  change halfLineEdge (thresholdSiteEnvironment p u) (n + 1) <
    halfLineEdge (thresholdSiteEnvironment q u) (n + 1)
  omega

/-- The east-site uniform, read from the lower edge, has its original law and is
independent of the event that the two edges have not yet split. -/
private theorem real_measure_east_hit {p q : unitInterval} (hpq : p ≤ q) (n : ℕ) :
    siteUniformLaw.real (noEdgeSplitThrough p q n ∩
      (fun u : Environment => u (thresholdEdgeSite p n u + (1, 0))) ⁻¹'
        Ioc (p : ℝ) (q : ℝ)) =
      siteUniformLaw.real (noEdgeSplitThrough p q n) * ((q : ℝ) - (p : ℝ)) := by
  classical
  let A := noEdgeSplitThrough p q n
  let G : Environment → ℝ := A.indicator (fun _ => 1)
  let F (u : Environment) := u ((1, 0) : Lattice)
  let F' (u : Environment) := u (thresholdEdgeSite p n u + (1, 0))
  let I := Ioc (p : ℝ) (q : ℝ)
  have hG : Measurable[levelsAtMost (n : ℤ)] G :=
    measurable_const.indicator (measurableSet_noEdgeSplitThrough_levels p q n)
  have hF : Measurable F := measurable_pi_apply _
  obtain ⟨hInd, hLaw⟩ := indepFun_identDistrib_shift_of_levelsAtMost siteUniformMarginal
    (n : ℤ) (thresholdEdgeSite p n) (measurable_thresholdEdgeSite_levels p n)
    (thresholdEdgeSite_level p n) F hF (fun _ _ h => h (1, 0) (by decide)) G hG
  have hA : G ⁻¹' ({1} : Set ℝ) = A := by
    ext u
    by_cases hu : u ∈ A <;> simp [G, hu]
  have hhit : siteUniformLaw (F' ⁻¹' I) = siteUniformMarginal I := by
    have eq₁ := Measure.map_apply_of_aemeasurable hLaw.aemeasurable_fst
      (measurableSet_Ioc : MeasurableSet I)
    have eq₂ := environmentLaw_map_eval siteUniformMarginal ((1, 0) : Lattice)
    change siteUniformLaw.map F = siteUniformMarginal at eq₂
    change siteUniformLaw.map F' I = siteUniformLaw (F' ⁻¹' I) at eq₁
    rw [← eq₁, show siteUniformLaw.map F' = siteUniformLaw.map F from hLaw.map_eq, eq₂]
  have hfactor := hInd.measure_inter_preimage_eq_mul ({1} : Set ℝ) I
    (measurableSet_singleton _) measurableSet_Ioc
  change siteUniformLaw (G ⁻¹' {1} ∩ F' ⁻¹' I) =
    siteUniformLaw (G ⁻¹' {1}) * siteUniformLaw (F' ⁻¹' I) at hfactor
  rw [hA, hhit] at hfactor
  change (siteUniformLaw (A ∩ F' ⁻¹' I)).toReal =
    (siteUniformLaw A).toReal * ((q : ℝ) - (p : ℝ))
  rw [hfactor, ENNReal.toReal_mul, ← siteUniformMarginal_real_Ioc p q hpq, Measure.real_def]

/-- At each step, conditional on no split so far, the chance of a first split is
at least the increase in density. -/
private theorem real_measure_noEdgeSplitThrough_succ {p q : unitInterval}
    (hp : 0 < (p : ℝ)) (hpq : p ≤ q) (n : ℕ) :
    siteUniformLaw.real (noEdgeSplitThrough p q (n + 1)) ≤
      (1 - ((q : ℝ) - (p : ℝ))) * siteUniformLaw.real (noEdgeSplitThrough p q n) := by
  let A := noEdgeSplitThrough p q n
  let B := A ∩ (fun u : Environment => u (thresholdEdgeSite p n u + (1, 0))) ⁻¹'
    Ioc (p : ℝ) (q : ℝ)
  have hmA : MeasurableSet A := levelsAtMost_le _ _ (measurableSet_noEdgeSplitThrough_levels p q n)
  have hmT : Measurable (thresholdEdgeSite p n) :=
    (measurable_thresholdEdgeSite_levels p n).mono (levelsAtMost_le _) le_rfl
  have hmF : Measurable (fun u : Environment => u (thresholdEdgeSite p n u + (1, 0))) := by
    have h : Measurable (fun x : Lattice × Environment => x.2 (x.1 + (1, 0))) :=
      measurable_from_prod_countable_right fun t => measurable_pi_apply (t + (1, 0))
    exact h.comp (hmT.prodMk measurable_id)
  have hmB : MeasurableSet B := hmA.inter (hmF measurableSet_Ioc)
  have hsub : B ⊆ A := inter_subset_left
  have hAE : noEdgeSplitThrough p q (n + 1) ≤ᵐ[siteUniformLaw] A \ B := by
    filter_upwards [ae_thresholdHalfLine_nonempty p hp] with u hu hn
    have ht : u ∈ A := fun j hj => hn j (hj.trans (Nat.le_succ n))
    refine ⟨ht, fun hB => hn (n + 1) le_rfl ?_⟩
    exact edgeSplit_succ_of_east hpq n u hu hB.2
  have hbound := ENNReal.toReal_mono (measure_ne_top siteUniformLaw (A \ B)) (measure_mono_ae hAE)
  change siteUniformLaw.real (noEdgeSplitThrough p q (n + 1)) ≤
    siteUniformLaw.real (A \ B) at hbound
  rw [measureReal_sdiff hsub hmB, show siteUniformLaw.real B =
    siteUniformLaw.real A * ((q : ℝ) - (p : ℝ)) from real_measure_east_hit hpq n] at hbound
  exact hbound.trans_eq (by ring)

/-- The chance of no first split through level `n` has the geometric upper bound
from the fresh east site at each step. -/
theorem real_measure_noEdgeSplitThrough_le {p q : unitInterval}
    (hp : 0 < (p : ℝ)) (hpq : p ≤ q) (n : ℕ) :
    siteUniformLaw.real (noEdgeSplitThrough p q n) ≤ (1 - ((q : ℝ) - (p : ℝ))) ^ n := by
  have hnonneg : 0 ≤ 1 - ((q : ℝ) - (p : ℝ)) := by
    linarith [p.2.1, q.2.2]
  induction n with
  | zero => simp [noEdgeSplitThrough_zero]
  | succ n ih =>
    rw [pow_succ']
    exact (real_measure_noEdgeSplitThrough_succ hp hpq n).trans
      (mul_le_mul_of_nonneg_left ih hnonneg)

end LPPDifferentiability.FinalDraft
