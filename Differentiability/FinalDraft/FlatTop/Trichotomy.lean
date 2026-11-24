/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatDensitySource.MeanRates
public import Differentiability.Frozen.FinalDraft.CriticalDensity
import Differentiability.FinalDraft.FlatBlockSource.Reopening
import Differentiability.FinalDraft.FlatDensitySource.DensityInterpolation
import Differentiability.FinalDraft.FlatTopRates.RightContinuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Bounds on the actual expected Bernoulli half-line rates in the three density regimes. -/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LPPDifferentiability.FinalDraft

/-- Positive Bernoulli origin survival bounds the critical density above. -/
private theorem criticalDensity_le_of_bernoulli_survival (p : unitInterval)
    (hp : 0 < environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) (orientedSiteSurvival 1)) :
    orientedSiteCriticalDensity ≤ (p : ℝ) := by
  unfold orientedSiteCriticalDensity
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro q ⟨r, rfl, _⟩
    exact r.2.1
  · exact ⟨p, rfl, hp⟩

/-- The critical expected rate infimum is one half, by right continuity and
reopening at any positive density whose rate exceeds one half. -/
theorem isGLB_halfLineEdge_at_criticalDensity :
    let pc : unitInterval := ⟨orientedSiteCriticalDensity,
      orientedSiteCriticalDensity_mem_Ioo.1.le, orientedSiteCriticalDensity_mem_Ioo.2.le⟩
    IsGLB (range fun n : ℕ => expectedBernoulliHalfLineEdge pc (n + 1) / ((n : ℝ) + 1))
      (1 / 2) := by
  intro pc
  let R := range fun n : ℕ => expectedBernoulliHalfLineEdge pc (n + 1) / ((n : ℝ) + 1)
  have hhalf : (1 / 2 : ℝ) ∈ lowerBounds R := by
    rintro _ ⟨n, rfl⟩
    apply (le_div_iff₀ (by positivity)).mpr
    have h := half_level_le_integral_halfLineEdge_criticalDensity (n + 1) (Nat.succ_pos n)
    unfold expectedBernoulliHalfLineEdge
    simpa only [Nat.cast_add, Nat.cast_one] using h
  obtain ⟨β, hβ⟩ : ∃ β, IsGLB R β :=
    ⟨sInf R, isGLB_csInf (range_nonempty _) ⟨1 / 2, hhalf⟩⟩
  have hle : β ≤ 1 / 2 := by
    apply le_of_not_gt
    intro hlt
    obtain ⟨q, _, hq, hsurv⟩ := exists_survival_below_of_halfLineEdge_speed pc
      orientedSiteCriticalDensity_mem_Ioo hlt hβ
    exact hq.not_ge (criticalDensity_le_of_bernoulli_survival q hsurv)
  have hβeq : β = 1 / 2 := le_antisymm hle (hβ.2 hhalf)
  exact hβeq ▸ hβ

/-- Above the critical density, strict density interpolation puts the finite
expected rate infimum strictly above one half. -/
theorem half_lt_of_isGLB_halfLineEdge_of_criticalDensity_lt (p : unitInterval)
    (hp : orientedSiteCriticalDensity < (p : ℝ)) {β : ℝ}
    (hβ : IsGLB (range fun n : ℕ =>
      expectedBernoulliHalfLineEdge p (n + 1) / ((n : ℝ) + 1)) β) :
    1 / 2 < β := by
  let pc : unitInterval := ⟨orientedSiteCriticalDensity,
    orientedSiteCriticalDensity_mem_Ioo.1.le, orientedSiteCriticalDensity_mem_Ioo.2.le⟩
  exact isGLB_halfLineEdge_bernoulli_lt_of_density_lt
    (p := pc) (q := p) orientedSiteCriticalDensity_mem_Ioo.1 hp
    isGLB_halfLineEdge_at_criticalDensity hβ

/-- A positive subcritical density cannot have a finite expected rate infimum
at least one half. A strictly larger subcritical density would have a greater
infimum, and reopening there would give subcritical survival. -/
theorem lt_half_of_isGLB_halfLineEdge_of_lt_criticalDensity (p : unitInterval)
    (hp₀ : 0 < (p : ℝ)) (hp : (p : ℝ) < orientedSiteCriticalDensity) {β : ℝ}
    (hβ : IsGLB (range fun n : ℕ =>
      expectedBernoulliHalfLineEdge p (n + 1) / ((n : ℝ) + 1)) β) :
    β < 1 / 2 := by
  let q₀ : ℝ := ((p : ℝ) + orientedSiteCriticalDensity) / 2
  have hpq₀ : (p : ℝ) < q₀ := by dsimp only [q₀]; linarith only [hp]
  have hq₀ : q₀ < orientedSiteCriticalDensity := by dsimp only [q₀]; linarith only [hp]
  have hq : q₀ ∈ Ioo (0 : ℝ) 1 :=
    ⟨hp₀.trans hpq₀, hq₀.trans orientedSiteCriticalDensity_mem_Ioo.2⟩
  let q : unitInterval := ⟨q₀, hq.1.le, hq.2.le⟩
  have hpq : p < q := hpq₀
  let Rq := range fun n : ℕ => expectedBernoulliHalfLineEdge q (n + 1) / ((n : ℝ) + 1)
  have hBdd : BddBelow Rq := by
    refine ⟨β, ?_⟩
    rintro _ ⟨n, rfl⟩
    apply (hβ.1 (mem_range_self n)).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hbase₀ : 0 ≤ 1 - ((q : ℝ) - (p : ℝ)) :=
      sub_nonneg.mpr ((sub_le_self (q : ℝ) p.2.1).trans q.2.2)
    have hbase₁ : 1 - ((q : ℝ) - (p : ℝ)) ≤ 1 := sub_le_self _ (sub_nonneg.mpr hpq.le)
    exact sub_nonneg.mp ((sub_nonneg.mpr (pow_le_one₀ hbase₀ hbase₁)).trans
      (one_sub_pow_le_expectedBernoulliHalfLineEdge_sub hp₀ hpq.le (n + 1)))
  have hγ : IsGLB Rq (sInf Rq) := isGLB_csInf (range_nonempty _) hBdd
  have hinc : β < sInf Rq := isGLB_halfLineEdge_bernoulli_lt_of_density_lt hp₀ hpq hβ hγ
  apply lt_of_not_ge
  intro hβhalf
  obtain ⟨r, _, hr, hsurv⟩ := exists_survival_below_of_halfLineEdge_speed q hq
    (hβhalf.trans_lt hinc) hγ
  exact (hr.trans hq₀).not_ge (criticalDensity_le_of_bernoulli_survival r hsurv)

end LPPDifferentiability.FinalDraft
