/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatTop.Percolation
public import Differentiability.Probability.TopIndicatorLaw
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import all Differentiability.FinalDraft.FlatTop.OriginEdge
import all Differentiability.FinalDraft.FlatTop.SurvivalLaw
import Differentiability.FinalDraft.FlatTop.HalfLineSpeed
import Differentiability.FinalDraft.FlatTop.SpeedTransfer
import all Differentiability.Probability.HalfLineEdgeDeviation
import Differentiability.Model.OrientedPercolationLaws
import LPP_Foundations.Model.Paths.Swap
import LPP_Foundations.Probability.EnvironmentSwap
import Mathlib.Tactic.Linarith

/-!
# Lower bounds on expected edge rates from origin survival

The half-line and its reflection both reach the surviving origin's endpoints.
If a fixed-block mean were below half its length, the two exponential upper
deviation bounds would force survival probability zero.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace LPPDifferentiability.FinalDraft

/-- Positive survival requires positive probability of a top site. -/
theorem singleton_one_measure_pos_of_orientedSiteSurvival_pos (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : 0 < environmentLaw ν (orientedSiteSurvival 1)) :
    0 < ν {1} := by
  by_contra! hν0
  let A (z : Lattice) : Set Environment := {ω | ω z = 1}
  have hNull (z : Lattice) : environmentLaw ν (A z) = 0 := by
    change environmentLaw ν ((fun ω : Environment => ω z) ⁻¹' ({1} : Set ℝ)) = 0
    rw [← Measure.map_apply (measurable_environment_eval z) (measurableSet_singleton _),
      environmentLaw_map_eval]
    exact le_antisymm hν0 bot_le
  have hsub : orientedSiteSurvival 1 ⊆ A (1, 0) ∪ A (0, 1) := by
    rintro ω ⟨γ, hzero, hstep, hopen⟩
    have hfirst : γ 1 = (1, 0) ∨ γ 1 = (0, 1) := by
      simpa only [hzero, zero_add] using hstep 0
    rcases hfirst with he | hn
    · exact Or.inl (he ▸ hopen 0)
    · exact Or.inr (hn ▸ hopen 0)
  have hz : environmentLaw ν (orientedSiteSurvival 1) ≤ 0 := by
    calc
      _ ≤ environmentLaw ν (A (1, 0) ∪ A (0, 1)) := measure_mono hsub
      _ ≤ environmentLaw ν (A (1, 0)) + environmentLaw ν (A (0, 1)) :=
        measure_union_le _ _
      _ = 0 := by rw [hNull, hNull, add_zero]
  exact (not_lt_of_ge hz) hν

/-- A path from the origin through top sites is a competitor for the half-line edge. -/
private theorem fst_le_halfLineEdge_of_open_path (ω : Environment) (n : ℕ)
    (d : ℕ × ℕ) (hd : d.1 + d.2 = n) (q : Path 0 d)
    (hopen : ∀ i : Fin (d.1 + d.2 + 1), 0 < i.val → ω (q.vertex i) = 1) :
    (d.1 : ℤ) ≤ halfLineEdge ω n := by
  have hv : ((d.1 : ℤ), (d.2 : ℤ)) ∈ openReachSet (topSites ω) antidiagHalfLine n := by
    refine ⟨0, ?_, ⟨d, zero_add _, q, fun i => hopen i.succ (by simp)⟩, ?_⟩
    · simp [antidiagHalfLine]
    · simp only [Prod.fst_zero, Prod.snd_zero, zero_add, ← Nat.cast_add, hd]
  exact le_maxFirst _ (by
    refine ⟨0 + n, ?_⟩
    rintro _ ⟨v, hv', rfl⟩
    exact bddAbove_fst_openReachSet _ _ _ 0 (fun u hu => hu.2) v hv') hv

/-- On survival the two half-line edges dominate the coordinates of one common level endpoint. -/
private theorem level_le_halfLineEdge_add_swap_of_survival (ω : Environment)
    (hω : ω ∈ orientedSiteSurvival 1) (n : ℕ) :
    (n : ℤ) ≤ halfLineEdge ω n + halfLineEdge (environmentSwap ω) n := by
  obtain ⟨d, hd, q, hopen⟩ := exists_open_prefix_of_orientedSiteSurvival hω n
  have hfst := fst_le_halfLineEdge_of_open_path ω n d hd q hopen
  have hswap : ∀ i : Fin (d.swap.1 + d.swap.2 + 1), 0 < i.val →
      environmentSwap ω (q.swap.vertex i) = 1 := by
    intro i hi
    rw [Path.swap_vertex, environmentSwap_apply, Prod.swap_swap]
    exact hopen _ (by simpa only [Fin.val_cast] using hi)
  have hsnd := fst_le_halfLineEdge_of_open_path (environmentSwap ω) n d.swap
    (by simpa only [Prod.fst_swap, Prod.snd_swap, Nat.add_comm] using hd) q.swap hswap
  simp only [Prod.fst_swap] at hsnd
  omega

/-- Positive origin survival forces every positive-length expected half-line edge to advance at
least half the level length, in the first-coordinate normalization. -/
theorem half_level_le_integral_halfLineEdge_of_survival_pos (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : 0 < environmentLaw ν (orientedSiteSurvival 1))
    (L : ℕ) (hL : 0 < L) :
    (1 / 2 : ℝ) * L ≤ ∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw ν := by
  by_contra! hmean
  have hp := singleton_one_measure_pos_of_orientedSiteSurvival_pos ν hν
  obtain ⟨A, B, _, hB, htail⟩ := halfLineEdge_upper_deviation ν hp (1 / 2) L hL hmean
  let E (n : ℕ) : Set Environment := {ω | (1 / 2 : ℝ) * n ≤ (halfLineEdge ω n : ℝ)}
  have hEm (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_le measurable_const
      ((Measurable.of_discrete (f := fun x : ℤ => (x : ℝ))).comp (measurable_halfLineEdge n))
  have hCover (n : ℕ) : orientedSiteSurvival 1 ⊆ E n ∪ environmentSwap ⁻¹' E n := by
    intro ω hω
    have hsum := level_le_halfLineEdge_add_swap_of_survival ω hω n
    have hreal : (n : ℝ) ≤ (halfLineEdge ω n : ℝ) + (halfLineEdge (environmentSwap ω) n : ℝ) := by
      exact_mod_cast hsum
    by_cases hωE : ω ∈ E n
    · exact Or.inl hωE
    · refine Or.inr ?_
      change (1 / 2 : ℝ) * n ≤ (halfLineEdge (environmentSwap ω) n : ℝ)
      change ¬ (1 / 2 : ℝ) * n ≤ (halfLineEdge ω n : ℝ) at hωE
      linarith only [hreal, lt_of_not_ge hωE]
  have hsurvBound (n : ℕ) :
      (environmentLaw ν).real (orientedSiteSurvival 1) ≤
        A * Real.exp (-(B * n)) + A * Real.exp (-(B * n)) := by
    have hswap : (environmentLaw ν).real (environmentSwap ⁻¹' E n) =
        (environmentLaw ν).real (E n) := by
      rw [← map_measureReal_apply measurable_environmentSwap (hEm n),
        environmentLaw_map_environmentSwap]
    calc
      _ ≤ (environmentLaw ν).real (E n ∪ environmentSwap ⁻¹' E n) :=
        measureReal_mono (hCover n)
      _ ≤ (environmentLaw ν).real (E n) + (environmentLaw ν).real (environmentSwap ⁻¹' E n) :=
        measureReal_union_le _ _
      _ ≤ _ := by
        rw [hswap]
        exact add_le_add (htail n) (htail n)
  have hdecay : Tendsto (fun n : ℕ => A * Real.exp (-(B * n))) atTop (𝓝 0) := by
    have hneg : Tendsto (fun n : ℕ => -(B * (n : ℝ))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hB)
    simpa only [Function.comp_def, mul_zero] using (Real.tendsto_exp_atBot.comp hneg).const_mul A
  have hsum : Tendsto (fun n : ℕ => A * Real.exp (-(B * n)) + A * Real.exp (-(B * n)))
      atTop (𝓝 0) := by
    simpa only [add_zero] using hdecay.add hdecay
  have hzero : (environmentLaw ν).real (orientedSiteSurvival 1) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hsum (Eventually.of_forall hsurvBound)
  exact hzero.not_gt (ENNReal.toReal_pos_iff.mpr ⟨hν, measure_lt_top _ _⟩)

/-- Positive survival at a Bernoulli density strictly above the survival threshold. -/
theorem measure_orientedSiteSurvival_bernoulli_pos_of_critical_lt (p : unitInterval)
    (hp : orientedSiteCriticalDensity < (p : ℝ)) :
    0 < environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) (orientedSiteSurvival 1) := by
  let S : Set ℝ := {q | ∃ r : unitInterval, (r : ℝ) = q ∧
    0 < environmentLaw (bernoulliMeasure (1 : ℝ) 0 r) (orientedSiteSurvival 1)}
  obtain ⟨q, _, hq⟩ := exists_bernoulli_survival_below_one
  have hne : S.Nonempty := ⟨q, q, rfl, hq⟩
  obtain ⟨_, ⟨r, hr, hsurv⟩, hlt⟩ := exists_lt_of_csInf_lt hne (show sInf S < p from hp)
  have hrp : r ≤ p := by
    change (r : ℝ) ≤ (p : ℝ)
    exact hr.trans_le hlt.le
  exact hsurv.trans_le (orientedSiteSurvival_bernoulli_mono hrp)

/-- On positive survival the actual origin speed is at least one half and is the infimum
of the expected half-line rates. -/
theorem exists_originRightEdgeSpeed_of_survival_pos (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : 0 < environmentLaw ν (orientedSiteSurvival 1)) :
    ∃ β : ℝ, 1 / 2 ≤ β ∧ IsGLB (Set.range fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)) β ∧
      IsOriginRightEdgeSpeed ν 1 β := by
  have hhalf : (1 / 2 : ℝ) ∈ lowerBounds (Set.range (fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1))) := by
    rintro _ ⟨n, rfl⟩
    have hL := half_level_le_integral_halfLineEdge_of_survival_pos ν hν (n + 1) (Nat.succ_pos n)
    rw [Nat.cast_add, Nat.cast_one] at hL
    exact (le_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr hL
  obtain ⟨β, hGLB, hlim⟩ := exists_constant_halfLineEdge_speed_of_bddBelow ν
    (singleton_one_measure_pos_of_orientedSiteSurvival_pos ν hν) ⟨1 / 2, hhalf⟩
  exact ⟨β, hGLB.2 hhalf, hGLB, isOriginRightEdgeSpeed_of_halfLine_limit ν β hlim⟩

/-- When the top atom is above the critical density, the original field's actual origin speed
agrees with the infimum of the half-line rates of its Bernoulli indicator field. -/
theorem exists_originRightEdgeSpeed_of_critical_lt_topAtom
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (M : ℝ) (hM : (M : EReal) = supportTop μ)
    (hp : orientedSiteCriticalDensity < μ.real {M}) :
    let ν := bernoulliMeasure (1 : ℝ) 0 ⟨μ.real {M}, by simp⟩
    0 < environmentLaw μ (orientedSiteSurvival M) ∧
      ∃ β : ℝ, 1 / 2 ≤ β ∧ IsGLB (Set.range fun n : ℕ =>
        (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)) β ∧
        IsOriginRightEdgeSpeed μ M β := by
  intro ν
  have hsurv := measure_orientedSiteSurvival_pos_of_criticalDensity_lt μ M hM hp
  have hν : 0 < environmentLaw ν (orientedSiteSurvival 1) := by
    simpa only [ν, ← measure_orientedSiteSurvival_eq_bernoulli μ M hM] using hsurv
  obtain ⟨β, hhalf, hGLB, hβ⟩ := exists_originRightEdgeSpeed_of_survival_pos ν hν
  exact ⟨hsurv, β, hhalf, hGLB, isOriginRightEdgeSpeed_of_bernoulli μ M hM hβ⟩

end LPPDifferentiability.FinalDraft
