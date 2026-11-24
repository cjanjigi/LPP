/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatTop.SurvivalLaw
public import Differentiability.FinalDraft.FlatTopRates.SurvivalRates
public import Differentiability.FinalDraft.FlatTopRates.UniformSiteCoupling
import all Differentiability.Probability.HalfLineEdgeDeviation
import Differentiability.Model.OrientedPercolationLaws
import LPP_Foundations.Model.Paths.Geometry
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.Linarith

/-!
# Right continuity of fixed-length half-line expectations

At a fixed positive density, the half-line reaches the given level almost surely.
All paths that can reach at least that edge lie in a finite, sample-dependent
rectangle. The open sites in the rectangle stabilize when the threshold approaches
from above. The fixed starting-density edge and the level bound dominate the
edges at larger thresholds.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace LPPDifferentiability.FinalDraft

/-- The half-line reach set at a fixed level has a bounded first coordinate. -/
private theorem bddAbove_fst_halfLineReach (ω : Environment) (n : ℕ) :
    BddAbove (Prod.fst '' openReachSet (topSites ω) antidiagHalfLine n) := by
  refine ⟨0 + n, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact bddAbove_fst_openReachSet _ _ _ 0 (fun u hu => hu.2) v hv

/-- Adding top sites moves the half-line edge to the right whenever the lower process reaches the
level. The edge on the lower process is a true maximum in this case. -/
theorem halfLineEdge_mono_of_topSites_subset {ω η : Environment} (n : ℕ)
    (hω : (openReachSet (topSites ω) antidiagHalfLine n).Nonempty)
    (hsub : topSites ω ⊆ topSites η) : halfLineEdge ω n ≤ halfLineEdge η n := by
  have hs := openReachSet_mono hsub (subset_rfl : antidiagHalfLine ⊆ antidiagHalfLine) n
  exact csSup_le_csSup (bddAbove_fst_halfLineReach η n)
    (hω.image Prod.fst) (image_mono hs)

/-- The finite rectangle containing any path from the left half-line to level `n` whose first
coordinate at its end is at least `a`. -/
private def halfLineCompetitorSites (a : ℤ) (n : ℕ) : Finset Lattice :=
  Finset.Icc ((a - (n : ℤ), 0) : Lattice) ((n : ℤ), (n : ℤ) - a)

/-- Every vertex of a competitor at or to the right of `a` lies in the finite rectangle. -/
private theorem vertex_mem_halfLineCompetitorSites {u v : Lattice} {d : ℕ × ℕ} {n : ℕ}
    (q : Path u d) (hu : u ∈ antidiagHalfLine)
    (hv : v.1 + v.2 = u.1 + u.2 + n)
    (hd : u + ((d.1 : ℤ), (d.2 : ℤ)) = v) (a : ℤ) (ha : a ≤ v.1)
    (i : Fin (d.1 + d.2 + 1)) :
    q.vertex i ∈ halfLineCompetitorSites a n := by
  have huLev : u.1 + u.2 = 0 := hu.1
  have hux : u.1 ≤ 0 := hu.2
  have hd₁ := congrArg Prod.fst hd
  have hd₂ := congrArg Prod.snd hd
  simp only [Prod.fst_add, Prod.snd_add] at hd₁ hd₂
  have hcoord := q.vertex_mem_Icc i
  rw [hd] at hcoord
  have hlow : u ≤ q.vertex i := hcoord.1
  have hhigh : q.vertex i ≤ v := hcoord.2
  exact Finset.mem_Icc.mpr
    ⟨⟨by have := hlow.1; omega, by have := hlow.2; omega⟩,
      ⟨by have := hhigh.1; omega, by have := hhigh.2; omega⟩⟩

/-- If a larger open field agrees with the original on the finite rectangle, their
half-line edges agree at the given level. -/
private theorem halfLineEdge_eq_of_agree_on_competitors {ω η : Environment} (n : ℕ)
    (hω : (openReachSet (topSites ω) antidiagHalfLine n).Nonempty)
    (hsub : topSites ω ⊆ topSites η)
    (hagree : ∀ z ∈ halfLineCompetitorSites (halfLineEdge ω n) n,
      z ∈ topSites η → z ∈ topSites ω) :
    halfLineEdge η n = halfLineEdge ω n := by
  have hs := openReachSet_mono hsub (subset_rfl : antidiagHalfLine ⊆ antidiagHalfLine) n
  have hle := halfLineEdge_mono_of_topSites_subset n hω hsub
  obtain ⟨v, hv, hmax⟩ := maxFirst_mem _ (hω.mono hs) (bddAbove_fst_halfLineReach η n)
  have hmax' : v.1 = halfLineEdge η n := hmax
  have ha : halfLineEdge ω n ≤ v.1 := hmax' ▸ hle
  apply le_antisymm _ hle
  rw [← hmax']
  apply le_maxFirst _ (bddAbove_fst_halfLineReach ω n)
  obtain ⟨u, hu, ⟨d, hd, q, hopen⟩, hv⟩ := hv
  refine ⟨u, hu, ⟨d, hd, q, fun i => ?_⟩, hv⟩
  exact hagree _ (vertex_mem_halfLineCompetitorSites q hu hv hd _ ha i.succ) (hopen i)

/-- A fixed uniform coordinate's status stabilizes as the density approaches from above. -/
private theorem eventually_topSites_thresholdSiteEnvironment_agree (u : Environment)
    (p : unitInterval) (z : Lattice) :
    ∀ᶠ q in 𝓝[Ici p] p,
      z ∈ topSites (thresholdSiteEnvironment q u) ↔ z ∈ topSites (thresholdSiteEnvironment p u) := by
  by_cases hz : u z ≤ (p : ℝ)
  · filter_upwards [self_mem_nhdsWithin] with q hq
    rw [mem_topSites_thresholdSiteEnvironment_iff, mem_topSites_thresholdSiteEnvironment_iff]
    exact iff_of_true (hz.trans (show (p : ℝ) ≤ (q : ℝ) from hq)) hz
  · have hT : Tendsto (fun q : unitInterval => (q : ℝ)) (𝓝[Ici p] p) (𝓝 (p : ℝ)) :=
      (continuous_subtype_val.tendsto p).mono_left nhdsWithin_le_nhds
    filter_upwards [hT.eventually (gt_mem_nhds (lt_of_not_ge hz))] with q hq
    rw [mem_topSites_thresholdSiteEnvironment_iff, mem_topSites_thresholdSiteEnvironment_iff]
    exact iff_of_false (not_le.mpr hq) hz

/-- The actual half-line edge at a fixed level stabilizes under right approach on each sample
where the starting-density field reaches that level. -/
private theorem eventually_halfLineEdge_thresholdSiteEnvironment_eq (u : Environment)
    (p : unitInterval) (n : ℕ)
    (h : (openReachSet (topSites (thresholdSiteEnvironment p u)) antidiagHalfLine n).Nonempty) :
    ∀ᶠ q in 𝓝[Ici p] p, halfLineEdge (thresholdSiteEnvironment q u) n =
      halfLineEdge (thresholdSiteEnvironment p u) n := by
  let S := halfLineCompetitorSites (halfLineEdge (thresholdSiteEnvironment p u) n) n
  have hS : ∀ᶠ q in 𝓝[Ici p] p, ∀ z ∈ S,
      z ∈ topSites (thresholdSiteEnvironment q u) ↔ z ∈ topSites (thresholdSiteEnvironment p u) :=
    (eventually_all_finset S).mpr
      (fun z _ => eventually_topSites_thresholdSiteEnvironment_agree u p z)
  filter_upwards [self_mem_nhdsWithin, hS] with q hpq hagree
  apply halfLineEdge_eq_of_agree_on_competitors n h
    (topSites_thresholdSiteEnvironment_mono u (show p ≤ q from hpq))
  exact fun z hz => (hagree z hz).mp

/-- Every fixed-length expected half-line edge is right-continuous at positive density. -/
theorem continuousWithinAt_integral_halfLineEdge_bernoulli (p : unitInterval)
    (hp : 0 < (p : ℝ)) (n : ℕ) :
    ContinuousWithinAt (fun q : unitInterval =>
      ∫ ω, (halfLineEdge ω n : ℝ) ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0 q))
      (Ici p) p := by
  let F (q : unitInterval) (u : Environment) : ℝ := halfLineEdge (thresholdSiteEnvironment q u) n
  let ν := bernoulliMeasure (1 : ℝ) 0 p
  have hν1 : 0 < ν {1} := by
    rw [show ν {1} = (unitInterval.toNNReal p : ENNReal) from
      bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton _) (by simp) (by simp),
      ENNReal.coe_nnreal_eq, unitInterval.coe_toNNReal]
    exact ENNReal.ofReal_pos.mpr hp
  have hAE : ∀ᵐ u ∂siteUniformLaw,
      (openReachSet (topSites (thresholdSiteEnvironment p u)) antidiagHalfLine n).Nonempty := by
    have h := (ae_openReachSet_halfLine_infinite ν hν1).mono
      (fun ω hω => (hω n).nonempty)
    exact ae_of_ae_map (measurable_thresholdSiteEnvironment p).aemeasurable
      (by rwa [map_siteUniformLaw_thresholdSiteEnvironment])
  have hm : Measurable (fun ω : Environment => (halfLineEdge ω n : ℝ)) :=
    (Measurable.of_discrete (f := fun z : ℤ => (z : ℝ))).comp (measurable_halfLineEdge n)
  have hFint : Integrable (F p) siteUniformLaw := by
    have h : Integrable (fun ω : Environment => (halfLineEdge ω n : ℝ))
        (siteUniformLaw.map (thresholdSiteEnvironment p)) := by
      rw [map_siteUniformLaw_thresholdSiteEnvironment]
      exact integrable_halfLineEdge ν hν1 n
    exact h.comp_measurable (measurable_thresholdSiteEnvironment p)
  have hi (q : unitInterval) : (∫ u, F q u ∂siteUniformLaw) =
      ∫ ω, (halfLineEdge ω n : ℝ) ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0 q) := by
    rw [← map_siteUniformLaw_thresholdSiteEnvironment q]
    symm
    exact integral_map (measurable_thresholdSiteEnvironment q).aemeasurable
      hm.aestronglyMeasurable
  have ht : Tendsto (fun q => ∫ u, F q u ∂siteUniformLaw) (𝓝[Ici p] p)
      (𝓝 (∫ u, F p u ∂siteUniformLaw)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => |F p u| + n) (Eventually.of_forall fun q =>
        (hm.comp (measurable_thresholdSiteEnvironment q)).aestronglyMeasurable)
      ?_ (hFint.abs.add (integrable_const _)) ?_
    · filter_upwards [self_mem_nhdsWithin] with q hpq
      filter_upwards [hAE] with u hu
      have hlo : F p u ≤ F q u := by
        dsimp only [F]
        exact_mod_cast halfLineEdge_mono_of_topSites_subset n hu
          (topSites_thresholdSiteEnvironment_mono u (show p ≤ q from hpq))
      have hhi : F q u ≤ (n : ℝ) := by
        dsimp only [F]
        exact_mod_cast halfLineEdge_le (thresholdSiteEnvironment q u) n
      rw [Real.norm_eq_abs]
      exact abs_le.mpr
        ⟨by
          have hpabs : -|F p u| ≤ F p u := (abs_le.mp (le_refl |F p u|)).1
          linarith only [hlo, hpabs, Nat.cast_nonneg (α := ℝ) n],
          hhi.trans (le_add_of_nonneg_left (abs_nonneg _))⟩
    · filter_upwards [hAE] with u hu
      have he : (fun q => F q u) =ᶠ[𝓝[Ici p] p] (fun _ => F p u) :=
        (eventually_halfLineEdge_thresholdSiteEnvironment_eq u p n hu).mono
          (fun q h => congrArg (fun z : ℤ => (z : ℝ)) h)
      exact he.tendsto
  simpa only [ContinuousWithinAt, hi] using ht

/-- At the critical density, each expected half-line edge is at least half the level.
The conclusion follows by interpolation from the larger densities by right continuity. -/
theorem half_level_le_integral_halfLineEdge_criticalDensity (n : ℕ) (hn : 0 < n) :
    let p : unitInterval := ⟨orientedSiteCriticalDensity,
      ⟨orientedSiteCriticalDensity_mem_Ioo.1.le, orientedSiteCriticalDensity_mem_Ioo.2.le⟩⟩
    (1 / 2 : ℝ) * n ≤ ∫ ω, (halfLineEdge ω n : ℝ) ∂environmentLaw
      (bernoulliMeasure (1 : ℝ) 0 p) := by
  intro p
  have hp0 : 0 < (p : ℝ) := orientedSiteCriticalDensity_mem_Ioo.1
  have hp1 : p < 1 := orientedSiteCriticalDensity_mem_Ioo.2
  have : NeBot (𝓝[Ioi p] p) := nhdsGT_neBot_of_exists_gt ⟨1, hp1⟩
  have hT := (continuousWithinAt_integral_halfLineEdge_bernoulli p hp0 n).mono Ioi_subset_Ici_self
  have hWithin : ∀ᶠ q in 𝓝[Ioi p] p, q ∈ Ioi p := self_mem_nhdsWithin
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hT
    (hWithin.mono fun q hq => half_level_le_integral_halfLineEdge_of_survival_pos _
      (measure_orientedSiteSurvival_bernoulli_pos_of_critical_lt q hq) n hn)

end LPPDifferentiability.FinalDraft
