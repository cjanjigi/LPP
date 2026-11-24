/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatTop.Percolation
public import LPP_Foundations.Frozen.Model.Path
import Differentiability.Probability.PathBadSiteTail
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum

/-! Finite open paths taken from a surviving ray, and an elementary lower bound on the threshold. -/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace LPPDifferentiability.FinalDraft

/-- Each finite prefix of a surviving ray gives a finite path from the
origin whose sites after the origin are open. -/
theorem exists_open_prefix_of_orientedSiteSurvival {M : ℝ} {ω : Environment}
    (h : ω ∈ orientedSiteSurvival M) (n : ℕ) :
    ∃ d : ℕ × ℕ, d.1 + d.2 = n ∧
      ∃ q : Path 0 d, ∀ i : Fin (d.1 + d.2 + 1), 0 < i.val → ω (q.vertex i) = M := by
  obtain ⟨γ, hzero, hstep, hopen⟩ := h
  have hnonneg : (0 : Lattice) ≤ γ n := by
    rw [← hzero]
    exact hstep.monotone (Nat.zero_le n)
  let d : ℕ × ℕ := ((γ n).1.toNat, (γ n).2.toNat)
  have hd₁ : (d.1 : ℤ) = (γ n).1 := Int.toNat_of_nonneg hnonneg.1
  have hd₂ : (d.2 : ℤ) = (γ n).2 := Int.toNat_of_nonneg hnonneg.2
  have hlevel : (γ n).1 + (γ n).2 = (n : ℤ) := by
    simpa only [hzero, Prod.fst_zero, Prod.snd_zero, zero_add] using hstep.level n
  have hd : d.1 + d.2 = n := by omega
  let q : Path 0 d := {
    vertex := fun i => γ i.val
    start := hzero
    finish := by
      change γ (d.1 + d.2) = 0 + ((d.1 : ℤ), (d.2 : ℤ))
      rw [hd, zero_add]
      exact (Prod.ext hd₁ hd₂).symm
    step := fun i => hstep i.val }
  refine ⟨d, hd, q, fun i hi => ?_⟩
  change ω (γ i.val) = M
  have heq : i.val = (i.val - 1) + 1 := by omega
  rw [heq]
  exact hopen (i.val - 1)

/-- On survival the origin cluster reaches every level. -/
theorem openReachSet_origin_nonempty_of_survival {M : ℝ} {ω : Environment}
    (h : ω ∈ orientedSiteSurvival M) (n : ℕ) :
    (openReachSet {z | ω z = M} ({0} : Set Lattice) n).Nonempty := by
  obtain ⟨d, hd, q, hopen⟩ := exists_open_prefix_of_orientedSiteSurvival h n
  refine ⟨((d.1 : ℤ), (d.2 : ℤ)), 0, mem_singleton _, ⟨d, zero_add _, q, fun i => ?_⟩, ?_⟩
  · exact hopen i.succ (by simp)
  · simp only [Prod.fst_zero, Prod.snd_zero, zero_add, ← Nat.cast_add, hd]

/-- A surviving ray has at least `n` open collected sites in its
`n + 1` step prefix even if the initial site is closed. -/
private theorem survival_subset_many_open_sites (n : ℕ) :
    orientedSiteSurvival 1 ⊆ {ω : Environment |
      ∃ q : Σ i : Fin (n + 2), Path 0 (i.val, n + 1 - i.val),
        n ≤ (@Finset.filter Lattice (fun z => ω z ∈ ({1} : Set ℝ)) (Classical.decPred _)
          q.2.collectedSites).card} := by
  classical
  intro ω hω
  obtain ⟨d, hd, q, hopen⟩ := exists_open_prefix_of_orientedSiteSurvival hω (n + 1)
  have hsub : q.collectedSites.erase 0 ⊆
      q.collectedSites.filter (fun z => ω z ∈ ({1} : Set ℝ)) := by
    intro z hz
    obtain ⟨hz0, hzs⟩ := Finset.mem_erase.mp hz
    obtain ⟨i, hi⟩ := (q.mem_collectedSites_iff z).mp hzs
    refine Finset.mem_filter.mpr ⟨hzs, ?_⟩
    have hit : 0 < i.castSucc.val := by
      by_contra! hc
      have hic : i.castSucc = 0 := Fin.ext (Nat.eq_zero_of_le_zero hc)
      rw [hic, q.start] at hi
      exact hz0 hi.symm
    rw [← hi]
    exact mem_singleton_iff.mpr (hopen i.castSucc hit)
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (q.start_mem_collectedSites (by omega)), q.collectedSites_card,
    hd] at hcount
  let i : Fin (n + 2) := ⟨d.1, by omega⟩
  have hdisp : d = (i.val, n + 1 - i.val) := Prod.ext rfl (by dsimp [i]; omega)
  have hwitness : ∃ p : Path 0 (i.val, n + 1 - i.val),
      n ≤ (p.collectedSites.filter (fun z => ω z ∈ ({1} : Set ℝ))).card := by
    rw [← hdisp]
    exact ⟨q, by simpa using hcount⟩
  obtain ⟨p, hp⟩ := hwitness
  exact ⟨⟨i, p⟩, hp⟩

/-- A rough path count already gives zero survival probability for site
densities below one quarter. -/
theorem measure_orientedSiteSurvival_eq_zero_of_lt_one_quarter (p : unitInterval)
    (hp : (p : ℝ) < 1 / 4) :
    environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) (orientedSiteSurvival 1) = 0 := by
  let ν := bernoulliMeasure (1 : ℝ) 0 p
  have hm : ν {1} = ENNReal.ofReal (p : ℝ) := by
    rw [show ν {1} = (unitInterval.toNNReal p : ENNReal) from
      bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton _) (by simp) (by simp)]
    exact ENNReal.coe_nnreal_eq (unitInterval.toNNReal p)
  have hp' : (4 : ENNReal) * ν {1} < 1 := by
    rw [hm, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 by norm_num),
      ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2 (by linarith)
  have hbound (n : ℕ) :
      environmentLaw ν (orientedSiteSurvival 1) ≤ 4 * (4 * ν {1}) ^ n := by
    calc
      _ ≤ (4 ^ (n + 1) : ENNReal) * ν {1} ^ n :=
        (measure_mono (survival_subset_many_open_sites n)).trans
          (measure_exists_path_bad_collected_sites_ge_le ν {1} (measurableSet_singleton _)
            0 (n + 1) n)
      _ = _ := by rw [pow_succ, mul_pow]; ac_rfl
  have hlim : Tendsto (fun n : ℕ => (4 : ENNReal) * (4 * ν {1}) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hp')
        (Or.inr (by norm_num : (4 : ENNReal) ≠ ∞))
  exact le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hbound))
    bot_le

end LPPDifferentiability.FinalDraft
