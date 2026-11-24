/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatDensitySource.FirstSplit
import all Differentiability.FinalDraft.FlatTop.HalfLineConvergence
import Mathlib.Analysis.Subadditive

/-! The finite lower bound on the expected rates is their limit by subadditivity. -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace LPPDifferentiability.FinalDraft

/-- The expected actual half-line edge under the Bernoulli site law of the given density. -/
noncomputable def expectedBernoulliHalfLineEdge (p : unitInterval) (n : ℕ) : ℝ :=
  ∫ ω, (halfLineEdge ω n : ℝ) ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0 p)

/-- Restarting with the full left half-line and then averaging gives a subadditive mean. -/
private theorem subadditive_expectedBernoulliHalfLineEdge (p : unitInterval) (hp : 0 < (p : ℝ)) :
    Subadditive (expectedBernoulliHalfLineEdge p) := by
  intro m k
  let ν := bernoulliMeasure (1 : ℝ) 0 p
  have hν : 0 < ν {1} := bernoulli_singleton_one_pos p hp
  have hLaw := (restartedHalfLineEdge_identDistrib ν m k).comp
    (Measurable.of_discrete (f := fun z : ℤ => (z : ℝ)))
  change IdentDistrib (fun ω => (restartedHalfLineEdge m k ω : ℝ))
    (fun ω => (halfLineEdge ω k : ℝ)) (environmentLaw ν) (environmentLaw ν) at hLaw
  have hm := integrable_halfLineEdge ν hν m
  have hk := hLaw.symm.integrable_snd (integrable_halfLineEdge ν hν k)
  have hAE : ∀ᵐ ω ∂environmentLaw ν, (halfLineEdge ω (m + k) : ℝ) ≤
      (halfLineEdge ω m : ℝ) + (restartedHalfLineEdge m k ω : ℝ) :=
    (ae_halfLineEdge_add_le_restartedHalfLineEdge ν hν m k).mono fun ω h => by exact_mod_cast h
  have h := integral_mono_ae (integrable_halfLineEdge ν hν (m + k)) (hm.add hk) hAE
  change (∫ ω, (halfLineEdge ω (m + k) : ℝ) ∂environmentLaw ν) ≤
    ∫ ω, (halfLineEdge ω m : ℝ) + (restartedHalfLineEdge m k ω : ℝ) ∂environmentLaw ν at h
  rw [integral_add hm hk, hLaw.integral_eq] at h
  exact h

/-- With a finite infimum of the positive-time expected rates, those rates
converge to that same infimum. -/
theorem tendsto_expectedBernoulliHalfLineEdge_div (p : unitInterval) (hp : 0 < (p : ℝ))
    (β : ℝ) (hβ : IsGLB (range fun n : ℕ =>
      expectedBernoulliHalfLineEdge p (n + 1) / ((n : ℝ) + 1)) β) :
    Tendsto (fun n : ℕ => expectedBernoulliHalfLineEdge p n / (n : ℝ)) atTop (𝓝 β) := by
  let E := expectedBernoulliHalfLineEdge p
  have hsub : Subadditive E := subadditive_expectedBernoulliHalfLineEdge p hp
  have hrate (n : ℕ) : β ≤ E (n + 1) / ((n + 1 : ℕ) : ℝ) := by
    have h := hβ.1 (mem_range_self n)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hbd : BddBelow (range fun n : ℕ => E n / (n : ℝ)) := by
    refine ⟨min β 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero => simpa only [Nat.cast_zero, div_zero] using min_le_right β 0
    | succ n => exact (min_le_left β 0).trans (hrate n)
  have hset : (fun n : ℕ => E n / (n : ℝ)) '' Ici 1 =
      range (fun n : ℕ => E (n + 1) / ((n : ℝ) + 1)) := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hn' : 1 ≤ n := hn
      cases n with
      | zero => omega
      | succ n => exact ⟨n, by simp⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n + 1, by simp, by simp⟩
  have hlim : hsub.lim = β := by
    rw [Subadditive.lim, hset]
    exact (isGLB_csInf (range_nonempty _) ⟨β, hβ.1⟩).unique hβ
  simpa only [hlim] using hsub.tendsto_lim hbd

end LPPDifferentiability.FinalDraft
