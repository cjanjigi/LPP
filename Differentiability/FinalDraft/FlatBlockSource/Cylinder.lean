/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatTopRates.UniformSiteCoupling
import LPP_Foundations.Probability.CoordinateLaw
import Mathlib.Tactic

/-! Continuity of the probability of a fixed finite site event in the
density, as used by Durrett (1984), p. 1026. -/

public section

open MeasureTheory ProbabilityTheory Set

namespace LPPDifferentiability.FinalDraft.FlatBlockSource

/-- A finite open-site event is measurable. -/
theorem measurableSet_of_open_sites (S : Finset Lattice) (A : Set Environment)
    (hA : ∀ ω ω' : Environment, (∀ z ∈ S, ω z = 1 ↔ ω' z = 1) → (ω ∈ A ↔ ω' ∈ A)) :
    MeasurableSet A := by
  classical
  let read (ω : Environment) (z : {z // z ∈ S}) : Bool := decide (ω z.val = 1)
  let write (bits : {z // z ∈ S} → Bool) : Environment :=
    fun z => if h : z ∈ S then if bits ⟨z, h⟩ then 1 else 0 else 0
  have hread : Measurable read := by
    refine Measurable.of_eval fun z => ?_
    change Measurable (fun (ω : Environment) => decide (ω z.val = 1))
    have heq : (fun ω : Environment => decide (ω z.val = 1)) =
        (fun ω : Environment => if ω z.val = 1 then true else false) := by
      funext ω
      by_cases h : ω z.val = 1 <;> simp [h]
    rw [heq]
    exact Measurable.ite ((measurable_environment_eval _) (measurableSet_singleton _))
      measurable_const measurable_const
  have heq : A = read ⁻¹' (write ⁻¹' A) := by
    ext ω
    change ω ∈ A ↔ write (read ω) ∈ A
    apply hA
    intro z hz
    by_cases h : ω z = 1 <;> simp [read, write, hz, h]
  rw [heq]
  exact hread MeasurableSet.of_discrete

/-- The change in failure probability is bounded by the probability
that an indicator changes at some site of the fixed support. -/
theorem failure_le_of_lower_density (S : Finset Lattice) (A : Set Environment)
    (hA : ∀ ω ω' : Environment, (∀ z ∈ S, ω z = 1 ↔ ω' z = 1) → (ω ∈ A ↔ ω' ∈ A))
    {p q : unitInterval} (hqp : q ≤ p) :
    (environmentLaw (bernoulliMeasure (1 : ℝ) 0 q)).real (Aᶜ) ≤
      (environmentLaw (bernoulliMeasure (1 : ℝ) 0 p)).real (Aᶜ) +
        (S.card : ℝ) * ((p : ℝ) - (q : ℝ)) := by
  let E (z : Lattice) : Set Environment := (fun w : Environment => w z) ⁻¹' Ioc (q : ℝ) (p : ℝ)
  have hE (z : Lattice) : siteUniformLaw.real (E z) = (p : ℝ) - (q : ℝ) := by
    rw [Measure.real_def, siteUniformLaw, ← Measure.map_apply (measurable_environment_eval z)
      measurableSet_Ioc, environmentLaw_map_eval]
    exact siteUniformMarginal_real_Ioc q p hqp
  have hsub : thresholdSiteEnvironment q ⁻¹' Aᶜ ⊆
      (thresholdSiteEnvironment p ⁻¹' Aᶜ) ∪ ⋃ z ∈ S, E z := by
    intro ω hq
    by_cases h : ω ∈ ⋃ z ∈ S, E z
    · exact Or.inr h
    · refine Or.inl (fun hp => hq ((hA _ _ fun z hz => ?_).mp hp))
      have hno : ¬ ((q : ℝ) < ω z ∧ ω z ≤ (p : ℝ)) :=
        fun he => h (mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, he⟩⟩)
      have heq : ω z ≤ (p : ℝ) ↔ ω z ≤ (q : ℝ) :=
        ⟨fun hpz => le_of_not_gt (fun hqz => hno ⟨hqz, hpz⟩), fun hqz => hqz.trans hqp⟩
      change z ∈ topSites (thresholdSiteEnvironment p ω) ↔
        z ∈ topSites (thresholdSiteEnvironment q ω)
      rwa [mem_topSites_thresholdSiteEnvironment_iff, mem_topSites_thresholdSiteEnvironment_iff]
  have hsum : siteUniformLaw.real (⋃ z ∈ S, E z) ≤ (S.card : ℝ) * ((p : ℝ) - (q : ℝ)) := by
    calc
      _ ≤ ∑ z ∈ S, siteUniformLaw.real (E z) := measureReal_biUnion_finset_le S E
      _ = _ := by simp only [hE, Finset.sum_const, nsmul_eq_mul]
  have hm := (measurableSet_of_open_sites S A hA).compl
  simp only [← map_siteUniformLaw_thresholdSiteEnvironment, Measure.real_def,
    Measure.map_apply (measurable_thresholdSiteEnvironment _) hm]
  change siteUniformLaw.real (thresholdSiteEnvironment q ⁻¹' Aᶜ) ≤
    siteUniformLaw.real (thresholdSiteEnvironment p ⁻¹' Aᶜ) + _
  exact ((measureReal_mono hsub).trans (measureReal_union_le _ _)).trans
    (add_le_add_right hsum _)

/-- After the spatial scale is fixed, a strict upper bound on failure
persists at a strictly lower positive density. -/
theorem exists_lower_density (S : Finset Lattice) (A : Set Environment)
    (hA : ∀ ω ω' : Environment, (∀ z ∈ S, ω z = 1 ↔ ω' z = 1) → (ω ∈ A ↔ ω' ∈ A))
    {p : unitInterval} (hp : 0 < (p : ℝ)) {ζ : ℝ}
    (hζ : (environmentLaw (bernoulliMeasure (1 : ℝ) 0 p)).real (Aᶜ) < ζ) :
    ∃ q : unitInterval, 0 < (q : ℝ) ∧ (q : ℝ) < p ∧
      (environmentLaw (bernoulliMeasure (1 : ℝ) 0 q)).real (Aᶜ) ≤ ζ := by
  let margin := ζ - (environmentLaw (bernoulliMeasure (1 : ℝ) 0 p)).real (Aᶜ)
  have hm : 0 < margin := sub_pos.mpr hζ
  let d : ℝ := min ((p : ℝ) / 2) (margin / (2 * ((S.card : ℝ) + 1)))
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdp : d ≤ (p : ℝ) / 2 := min_le_left _ _
  let q : unitInterval := ⟨(p : ℝ) - d, ⟨by linarith, by linarith [p.property.2]⟩⟩
  have hq : (q : ℝ) = (p : ℝ) - d := rfl
  have hqp : q ≤ p := by show (q : ℝ) ≤ (p : ℝ); linarith
  refine ⟨q, by linarith, by linarith, (failure_le_of_lower_density S A hA hqp).trans ?_⟩
  have hdm : d * (2 * ((S.card : ℝ) + 1)) ≤ margin :=
    (le_div_iff₀ (by positivity : 0 < 2 * ((S.card : ℝ) + 1))).mp (min_le_right _ _)
  have hc : 0 ≤ (S.card : ℝ) * d := mul_nonneg (by positivity) hd.le
  rw [hq]
  dsimp only [margin] at hdm
  nlinarith only [hd, hdm, hc]

end LPPDifferentiability.FinalDraft.FlatBlockSource
