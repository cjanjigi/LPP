/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettSubadditive
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettRowLaws
public import ProbabilityBasics.Frozen.Foundations.Liggett.IsStationaryProcess
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettBlockProcess
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettBlockStationary
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettMomentCondition
public import ProbabilityBasics.Frozen.Foundations.Liggett.SeqShift
public import ProbabilityBasics.Frozen.Foundations.Liggett.IsErgodicProcess
public import ProbabilityBasics.Probability.LiggettConvergence
public import ProbabilityBasics.Probability.LiggettErgodic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Bounds.Basic

/-!
# Liggett's subadditive ergodic theorem

The theorem here is the proof of the statement in `Frozen/Foundations/Liggett/Theorem110.lean`
(Liggett (1985), Theorem 1.10). It follows from `exists_liggett_convergence` and
`exists_liggett_ergodic_convergence`, which need every `X 0 n` to be measurable. The statement in
`Frozen/` only assumes integrability, so row `0` is replaced by measurable functions that agree
with it almost surely. All other rows are unchanged.

## Main results

- `liggett_subadditive_ergodic`: the limit of `(1/n) E X_{0,n}` exists and equals the infimum,
  `X_{0,n}/n` converges almost surely and in `L¹`, and the limit is constant when the block
  processes are ergodic.

## References

- T. M. Liggett, *An improved subadditive ergodic theorem*, Ann. Probab. 13 (1985), Theorem 1.10.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace ProbabilityBasics.Full

open ProbabilityBasics.Liggett

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Liggett (1985), Theorem 1.10.** Suppose (1.7), (1.8), (1.9) and (1.3).
Then (1.4): `γ = lim (1/n) E X_{0,n} = inf_{n ≥ 1} (1/n) E X_{0,n}`;
(1.5): `X = lim X_{0,n}/n` exists almost surely and in `L¹`;
(1.6): `E X = γ`. If the stationary processes in (1.9) are ergodic,
then `X = γ` almost surely. -/
theorem liggett_subadditive_ergodic (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ)
    (h17 : LiggettSubadditive μ X) (h18 : LiggettRowLaws μ X)
    (h19 : LiggettBlockStationary μ X) (h13 : LiggettMomentCondition μ X) :
    ∃ γ : ℝ,
      -- (1.4)
      Tendsto (fun n : ℕ => (∫ ω, X 0 n ω ∂μ) / n) atTop (𝓝 γ) ∧
      IsGLB ((fun n : ℕ => (∫ ω, X 0 n ω ∂μ) / n) '' Ioi 0) γ ∧
      ∃ Xlim : Ω → ℝ, Measurable Xlim ∧ Integrable Xlim μ ∧
        -- (1.5), almost surely
        (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => X 0 n ω / n) atTop (𝓝 (Xlim ω))) ∧
        -- (1.5), in L¹
        Tendsto (fun n : ℕ => ∫ ω, |X 0 n ω / n - Xlim ω| ∂μ) atTop (𝓝 0) ∧
        -- (1.6)
        ∫ ω, Xlim ω ∂μ = γ ∧
        -- final clause
        ((∀ k : ℕ, 0 < k → IsErgodicProcess μ (liggettBlockProcess X k)) →
          ∀ᵐ ω ∂μ, Xlim ω = γ) := by
  classical
  obtain ⟨hint, c, hlower⟩ := h13
  -- Measurable versions of row 0.
  have hex : ∀ n : ℕ, ∃ F : Ω → ℝ, 0 < n → Measurable F ∧ X 0 n =ᵐ[μ] F := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨F, hF, hae⟩ := (hint n hn).aemeasurable
      exact ⟨F, fun _ => ⟨hF, hae⟩⟩
    · exact ⟨X 0 n, fun h => absurd h hn⟩
  choose F hF using hex
  let A : ℕ → ℕ → Ω → ℝ := fun m n => if m = 0 then F n else X m n
  have hA0 : ∀ n, A 0 n = F n := fun n => by simp [A]
  have hA : ∀ m n, m ≠ 0 → A m n = X m n := fun m n h => by simp [A, h]
  have hae0 : ∀ᵐ ω ∂μ, ∀ n : ℕ, 0 < n → X 0 n ω = A 0 n ω := by
    rw [ae_all_iff]
    intro n
    by_cases hn : 0 < n
    · filter_upwards [(hF n hn).2] with ω h _
      rw [hA0]
      exact h
    · exact Eventually.of_forall fun ω h => absurd h hn
  have hAmeas : ∀ n : ℕ, 0 < n → Measurable (A 0 n) := fun n hn => by
    rw [hA0]
    exact (hF n hn).1
  have hAint : ∀ n : ℕ, 0 < n → Integrable (A 0 n) μ := fun n hn => by
    rw [hA0]
    exact (hint n hn).congr (hF n hn).2
  have hmeaneq : ∀ n : ℕ, 0 < n → ∫ ω, A 0 n ω ∂μ = ∫ ω, X 0 n ω ∂μ := fun n hn => by
    rw [hA0]
    exact (integral_congr_ae (hF n hn).2).symm
  have hAlower : ∀ n : ℕ, 0 < n → -(c * (n : ℝ)) ≤ ∫ ω, A 0 n ω ∂μ := fun n hn => by
    rw [hmeaneq n hn]
    exact hlower n hn
  have hAsub : ∀ m n : ℕ, 0 < m → m < n →
      ∀ᵐ ω ∂μ, A 0 n ω ≤ A 0 m ω + A m n ω := by
    intro m n hm hmn
    filter_upwards [h17 m n hm hmn, hae0] with ω h hω
    rw [← hω n (by omega), ← hω m hm, hA m n hm.ne']
    exact h
  have hAadj : ∀ m : ℕ,
      IdentDistrib (fun ω (j : ℕ) => A (m + 1) (m + 1 + (j + 1)) ω)
        (fun ω (j : ℕ) => A m (m + (j + 1)) ω) μ μ := by
    intro m
    have h1 : (fun ω (j : ℕ) => A (m + 1) (m + 1 + (j + 1)) ω) =
        fun ω (j : ℕ) => X (m + 1) (m + 1 + (j + 1)) ω := by
      funext ω j
      exact congrFun (hA _ _ (Nat.succ_ne_zero m)) ω
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hseq : (fun ω (j : ℕ) => X 0 (0 + (j + 1)) ω) =ᵐ[μ]
          fun ω (j : ℕ) => A 0 (0 + (j + 1)) ω := by
        filter_upwards [hae0] with ω hω
        funext j
        exact hω _ (by omega)
      rw [h1]
      exact (h18 0).trans (IdentDistrib.of_ae_eq (h18 0).aemeasurable_snd hseq)
    · have h2 : (fun ω (j : ℕ) => A m (m + (j + 1)) ω) =
          fun ω (j : ℕ) => X m (m + (j + 1)) ω := by
        funext ω j
        exact congrFun (hA _ _ hm.ne') ω
      rw [h1, h2]
      exact h18 m
  have hblock : ∀ k : ℕ, 0 < k → ∀ j : ℕ,
      (fun ω => A ((j + 1) * k) ((j + 2) * k) ω) = liggettBlockProcess X k j := by
    intro k hk j
    funext ω
    exact congrFun (hA _ _ (by positivity)) ω
  have hAstat : ∀ k : ℕ, 0 < k → IdentDistrib
      (fun ω (j : ℕ) => A ((j + 2) * k) ((j + 3) * k) ω)
      (fun ω (j : ℕ) => A ((j + 1) * k) ((j + 2) * k) ω) μ μ := by
    intro k hk
    have e1 : (fun ω (j : ℕ) => A ((j + 2) * k) ((j + 3) * k) ω) =
        fun ω (n : ℕ) => liggettBlockProcess X k (n + 1) ω := by
      funext ω j
      exact congrFun (hblock k hk (j + 1)) ω
    have e2 : (fun ω (j : ℕ) => A ((j + 1) * k) ((j + 2) * k) ω) =
        fun ω (n : ℕ) => liggettBlockProcess X k n ω := by
      funext ω j
      exact congrFun (hblock k hk j) ω
    rw [e1, e2]
    exact h19 k hk
  obtain ⟨γ, g, hgm, hgi, hconv, hmean, hγ, hγinf, hL1⟩ :=
    LPPDifferentiability.exists_liggett_convergence μ A hAmeas hAint c hAlower
      hAsub hAadj hAstat
  have hγX : Tendsto (fun n : ℕ => (∫ ω, X 0 n ω ∂μ) / n) atTop (𝓝 γ) := by
    refine (tendsto_add_atTop_iff_nat 1).mp (hγ.congr fun n => ?_)
    rw [hmeaneq (n + 1) n.succ_pos]
  have hrange : (fun n : ℕ => (∫ ω, X 0 n ω ∂μ) / n) '' Ioi 0 =
      range (fun n : ℕ => (∫ ω, A 0 (n + 1) ω ∂μ) / ((n + 1 : ℕ) : ℝ)) := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have : 0 < n := hn; omega⟩
      exact ⟨k, by beta_reduce; rw [hmeaneq (k + 1) k.succ_pos]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k + 1, k.succ_pos, by beta_reduce; rw [hmeaneq (k + 1) k.succ_pos]⟩
  have hglb : IsGLB (range (fun n : ℕ =>
      (∫ ω, A 0 (n + 1) ω ∂μ) / ((n + 1 : ℕ) : ℝ))) γ := by
    have := isGLB_csInf (range_nonempty _) hγ.bddBelow_range
    rwa [← hγinf] at this
  have hconvX : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => X 0 n ω / n) atTop (𝓝 (g ω)) := by
    filter_upwards [hconv, hae0] with ω h hω
    refine (tendsto_add_atTop_iff_nat 1).mp (h.congr fun n => ?_)
    rw [hω (n + 1) n.succ_pos]
  have hL1X : Tendsto (fun n : ℕ => ∫ ω, |X 0 n ω / n - g ω| ∂μ) atTop (𝓝 0) := by
    refine (tendsto_add_atTop_iff_nat 1).mp (hL1.congr fun n => ?_)
    apply integral_congr_ae
    filter_upwards [hae0] with ω hω
    rw [hω (n + 1) n.succ_pos]
  refine ⟨γ, hγX, hrange ▸ hglb, g, hgm, hgi, hconvX, hL1X, hmean, ?_⟩
  intro herg
  have hErg : ∀ k : ℕ, 0 < k → Ergodic LPPDifferentiability.sequenceShift
      (μ.map (fun ω (j : ℕ) => A ((j + 1) * k) ((j + 2) * k) ω)) := by
    intro k hk
    have e : (fun ω (j : ℕ) => A ((j + 1) * k) ((j + 2) * k) ω) =
        fun ω (n : ℕ) => liggettBlockProcess X k n ω := by
      funext ω j
      exact congrFun (hblock k hk j) ω
    rw [e]
    exact herg k hk
  obtain ⟨γ', hγ'1, -, hae', -⟩ :=
    LPPDifferentiability.exists_liggett_ergodic_convergence μ A hAmeas hAint c
      hAlower hAsub hAadj hAstat hErg
  have hγeq : γ' = γ := tendsto_nhds_unique hγ'1 hγ
  filter_upwards [hconv, hae'] with ω h1 h2
  rw [tendsto_nhds_unique h1 h2, hγeq]

end ProbabilityBasics.Full
