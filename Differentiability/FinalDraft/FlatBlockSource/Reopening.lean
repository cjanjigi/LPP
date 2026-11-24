/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatTop.HalfLineSpeed
public import Differentiability.FinalDraft.FlatTop.Percolation
import Differentiability.FinalDraft.FlatBlockSource.HighProbability
import Differentiability.FinalDraft.FlatBlockSource.Survival
import Differentiability.Probability.HighDensityOrientedPaths
import Mathlib.Tactic

/-! Reopening of oriented site percolation by the full parallelogram
construction from Durrett (1984), Section 9. -/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LPPDifferentiability.FinalDraft

/-- A finite infimum of the actual half-line expected rates above one half
gives positive survival at a smaller positive Bernoulli density.
Durrett (1984), Section 9, pp. 1023–1026. -/
theorem exists_survival_below_of_halfLineEdge_speed (p : unitInterval)
    (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1) {β : ℝ} (hβ : 1 / 2 < β)
    (hglb : IsGLB (Set.range fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ)
        ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0 p)) / ((n : ℝ) + 1)) β) :
    ∃ q : unitInterval, 0 < (q : ℝ) ∧ (q : ℝ) < p ∧
      0 < environmentLaw (bernoulliMeasure (1 : ℝ) 0 q) (orientedSiteSurvival 1) := by
  let ν := bernoulliMeasure (1 : ℝ) 0 p
  have hν : 0 < ν {1} := by
    have hm : ν {1} = (unitInterval.toNNReal p : ℝ≥0∞) :=
      bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton _) (by simp) (by simp)
    rw [hm, ENNReal.coe_nnreal_eq]
    exact ENNReal.ofReal_pos.mpr hp.1
  obtain ⟨ζ, hζ, _, hcut⟩ := exists_high_density_oriented_path_cutoff 1
  obtain ⟨N, w, hN, hw, hbad⟩ := FlatBlockSource.exists_goodBlock_small_failure ν hν hβ hglb hζ
  let A := FlatBlockSource.GoodBlock N w 0
  obtain ⟨S, hS⟩ := FlatBlockSource.exists_finset_blockSupport N w hw.le 0
  have hAloc (ω ω' : Environment)
      (h : ∀ z ∈ S, ω z = 1 ↔ ω' z = 1) : ω ∈ A ↔ ω' ∈ A :=
    FlatBlockSource.goodBlock_local hN hw.le 0 ω ω' (fun z hz => h z ((hS z).mpr hz))
  obtain ⟨q, hq0, hqp, hq⟩ := FlatBlockSource.exists_lower_density S A hAloc hp.1 hbad
  let ρ := bernoulliMeasure (1 : ℝ) 0 q
  let G (v : ℕ × ℕ) := FlatBlockSource.GoodBlock N w (FlatBlockSource.anchor N w v)
  have hAm : MeasurableSet A := FlatBlockSource.measurableSet_of_open_sites S A hAloc
  have hG (v : ℕ × ℕ) : MeasurableSet (G v) := by
    change MeasurableSet (FlatBlockSource.GoodBlock N w (FlatBlockSource.anchor N w v))
    rw [FlatBlockSource.goodBlock_eq_translate]
    exact (environmentTranslationEquiv _).measurable hAm
  have hmarg (v : ℕ × ℕ) : (environmentLaw ρ).real ((G v)ᶜ) ≤ ζ := by
    dsimp only [G]
    rw [FlatBlockSource.goodBlock_eq_translate, ← preimage_compl]
    rw [(measurePreserving_environmentTranslationEquiv ρ (FlatBlockSource.anchor N w v)).measureReal_preimage
      hAm.compl.nullMeasurableSet]
    exact hq
  have hCoarse := hcut (environmentLaw ρ) G hG hmarg (fun T hT =>
    FlatBlockSource.independent_goodBlock hN hw ρ T hT)
  exact ⟨q, hq0, hqp, FlatBlockSource.measure_survival_pos_of_good_coarse_path hN hw ρ hCoarse.2⟩

end LPPDifferentiability.FinalDraft
