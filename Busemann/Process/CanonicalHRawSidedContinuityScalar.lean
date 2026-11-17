/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.CanonicalHRawSidedContinuityAux
public import Busemann.Geometry.CoalescingTiltTimeIndex

import Mathlib.Tactic

/-! Pointwise one-sided continuity of the literal scalar limits on actual H. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

private theorem tendsto_of_upper_brackets
    (a b : ℕ → ℝ) (l : ℝ)
    (ha : Tendsto a atTop (𝓝 l))
    (hbound : ∀ m, ∀ᶠ n in atTop, l ≤ b n ∧ b n ≤ a m) :
    Tendsto b atTop (𝓝 l) := by
  apply tendsto_order.2
  constructor
  · intro c hc
    filter_upwards [hbound 0] with n hn
    exact lt_of_lt_of_le hc hn.1
  · intro c hc
    obtain ⟨m, hm⟩ := (ha.eventually_lt_const hc).exists
    filter_upwards [hbound m] with n hn
    exact lt_of_le_of_lt hn.2 hm

private theorem tendsto_of_lower_brackets
    (a b : ℕ → ℝ) (l : ℝ)
    (ha : Tendsto a atTop (𝓝 l))
    (hbound : ∀ m, ∀ᶠ n in atTop, a m ≤ b n ∧ b n ≤ l) :
    Tendsto b atTop (𝓝 l) := by
  apply tendsto_order.2
  constructor
  · intro c hc
    obtain ⟨m, hm⟩ := (ha.eventually_const_lt hc).exists
    filter_upwards [hbound m] with n hn
    exact lt_of_lt_of_le hm hn.1
  · intro c hc
    filter_upwards [hbound 0] with n hn
    exact lt_of_le_of_lt hn.2 hc

-- The named parameters `hmoment`, `hμ` are part of the shared theorem interface.
set_option linter.unusedVariables false in
/-- Both literal scalar branches have the required one-sided limits along
arbitrary actual-H sequences. This is the deterministic edge-continuity step
for Strong Existence, lines 1194–1221. -/
theorem canonical_H_scalar_raw_sided_continuity
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (D : Set (CoalescingTilt μ))
    (left right : CoalescingTilt μ → ℕ → CoalescingTilt μ)
    (hSequences : ∀ h : CoalescingTilt μ,
      (h ∈ D → left h = (fun _ => h) ∧ right h = (fun _ => h)) ∧
      (h ∉ D →
        (∀ n, left h n ∈ D ∧ (left h n).val.1 < h.val.1) ∧
        StrictMono (fun n => (left h n).val.1) ∧
        Tendsto (left h) atTop (𝓝 h) ∧
        (∀ n, right h n ∈ D ∧ h.val.1 < (right h n).val.1) ∧
        StrictAnti (fun n => (right h n).val.1) ∧
        Tendsto (right h) atTop (𝓝 h)))
    (f : CoalescingTilt μ → ℝ)
    (hOrder : ∀ a b : CoalescingTilt μ, a ∈ D → b ∈ D →
      a.val.1 < b.val.1 → f b ≤ f a)
    (hSample : ∀ d : CoalescingTilt μ, d ∈ D →
      (∀ hs : ℕ → CoalescingTilt μ,
        (∀ n, hs n ∈ D ∧ (hs n).val.1 < d.val.1) →
        Tendsto hs atTop (𝓝 d) →
        Tendsto (fun n => f (hs n)) atTop (𝓝 (f d))) ∧
      (∀ hs : ℕ → CoalescingTilt μ,
        (∀ n, hs n ∈ D ∧ d.val.1 < (hs n).val.1) →
        Tendsto hs atTop (𝓝 d) →
        Tendsto (fun n => f (hs n)) atTop (𝓝 (f d)))) :
    (∀ h : CoalescingTilt μ, ∀ hs : ℕ → CoalescingTilt μ,
      (∀ n, (hs n).val.1 < h.val.1) → Tendsto hs atTop (𝓝 h) →
      Tendsto (fun n => limUnder atTop (fun m => f (left (hs n) m)))
        atTop (𝓝 (limUnder atTop (fun m => f (left h m)))) ∧
      Tendsto (fun n => limUnder atTop (fun m => f (right (hs n) m)))
        atTop (𝓝 (limUnder atTop (fun m => f (left h m))))) ∧
    (∀ h : CoalescingTilt μ, ∀ hs : ℕ → CoalescingTilt μ,
      (∀ n, h.val.1 < (hs n).val.1) → Tendsto hs atTop (𝓝 h) →
      Tendsto (fun n => limUnder atTop (fun m => f (left (hs n) m)))
        atTop (𝓝 (limUnder atTop (fun m => f (right h m)))) ∧
      Tendsto (fun n => limUnder atTop (fun m => f (right (hs n) m)))
        atTop (𝓝 (limUnder atTop (fun m => f (right h m))))) := by
  classical
  let L : CoalescingTilt μ → ℝ := fun h => limUnder atTop (fun n => f (left h n))
  let R : CoalescingTilt μ → ℝ := fun h => limUnder atTop (fun n => f (right h n))
  obtain ⟨hFinite, hWithin, hCross⟩ :=
    canonical_H_scalar_raw_limits_and_order μ D left right hSequences f hOrder
  have hAtSample (d : CoalescingTilt μ) (hd : d ∈ D) : L d = f d ∧ R d = f d := by
    have hl : Tendsto (fun n => f (left d n)) atTop (𝓝 (f d)) := by
      rw [((hSequences d).1 hd).1]
      exact tendsto_const_nhds
    have hr : Tendsto (fun n => f (right d n)) atTop (𝓝 (f d)) := by
      rw [((hSequences d).1 hd).2]
      exact tendsto_const_nhds
    exact ⟨hl.limUnder_eq, hr.limUnder_eq⟩
  have hCoordinate (h : CoalescingTilt μ) (v : ℕ → CoalescingTilt μ)
      (hv : Tendsto v atTop (𝓝 h)) :
      Tendsto (fun n => (v n).val.1) atTop (𝓝 h.val.1) :=
    ((continuous_fst.comp continuous_subtype_val).tendsto h).comp hv
  have hDiagonalLeft (h : CoalescingTilt μ) (v : ℕ → CoalescingTilt μ)
      (hvSide : ∀ n, (v n).val.1 < h.val.1)
      (hv : Tendsto v atTop (𝓝 h)) :
      ∃ d : ℕ → CoalescingTilt μ,
        (∀ n, d n ∈ D ∧ (d n = v n ∨ (d n).val.1 < (v n).val.1)) ∧
        Tendsto d atTop (𝓝 h) := by
    have hChoose (n : ℕ) : ∃ d : CoalescingTilt μ,
        d ∈ D ∧ (d = v n ∨ d.val.1 < (v n).val.1) ∧
          dist d (v n) < 1 / ((n : ℝ) + 1) := by
      by_cases hn : v n ∈ D
      · refine ⟨v n, hn, Or.inl rfl, ?_⟩
        simpa only [dist_self] using (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
      · rcases (hSequences (v n)).2 hn with ⟨hLeft, _, hLeftTendsto, _, _, _⟩
        have hr : 0 < 1 / ((n : ℝ) + 1) := by positivity
        obtain ⟨m, hm⟩ :=
          (hLeftTendsto.eventually (Metric.ball_mem_nhds _ hr)).exists
        refine ⟨left (v n) m, (hLeft m).1, Or.inr (hLeft m).2, ?_⟩
        simpa only [Metric.mem_ball] using hm
    choose d hd using hChoose
    have hdTendsto : Tendsto d atTop (𝓝 h) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      have hHalf : 0 < ε / 2 := by linarith
      have hvNear : ∀ᶠ n : ℕ in atTop, dist (v n) h < ε / 2 :=
        eventually_atTop.2 ((Metric.tendsto_atTop.mp hv) (ε / 2) hHalf)
      have hRadius : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hrNear : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / 2 :=
        hRadius.eventually (Iio_mem_nhds hHalf)
      have hNear : ∀ᶠ n : ℕ in atTop, dist (d n) h < ε := by
        filter_upwards [hvNear, hrNear] with n hn hr
        have htri := dist_triangle (d n) (v n) h
        linarith only [(hd n).2.2, hn, hr, htri]
      exact eventually_atTop.1 hNear
    exact ⟨d, fun n => ⟨(hd n).1, (hd n).2.1⟩, hdTendsto⟩
  have hDiagonalRight (h : CoalescingTilt μ) (v : ℕ → CoalescingTilt μ)
      (hvSide : ∀ n, h.val.1 < (v n).val.1)
      (hv : Tendsto v atTop (𝓝 h)) :
      ∃ d : ℕ → CoalescingTilt μ,
        (∀ n, d n ∈ D ∧ (d n = v n ∨ (v n).val.1 < (d n).val.1)) ∧
        Tendsto d atTop (𝓝 h) := by
    have hChoose (n : ℕ) : ∃ d : CoalescingTilt μ,
        d ∈ D ∧ (d = v n ∨ (v n).val.1 < d.val.1) ∧
          dist d (v n) < 1 / ((n : ℝ) + 1) := by
      by_cases hn : v n ∈ D
      · refine ⟨v n, hn, Or.inl rfl, ?_⟩
        simpa only [dist_self] using (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
      · rcases (hSequences (v n)).2 hn with ⟨_, _, _, hRight, _, hRightTendsto⟩
        have hr : 0 < 1 / ((n : ℝ) + 1) := by positivity
        obtain ⟨m, hm⟩ :=
          (hRightTendsto.eventually (Metric.ball_mem_nhds _ hr)).exists
        refine ⟨right (v n) m, (hRight m).1, Or.inr (hRight m).2, ?_⟩
        simpa only [Metric.mem_ball] using hm
    choose d hd using hChoose
    have hdTendsto : Tendsto d atTop (𝓝 h) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      have hHalf : 0 < ε / 2 := by linarith
      have hvNear : ∀ᶠ n : ℕ in atTop, dist (v n) h < ε / 2 :=
        eventually_atTop.2 ((Metric.tendsto_atTop.mp hv) (ε / 2) hHalf)
      have hRadius : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hrNear : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / 2 :=
        hRadius.eventually (Iio_mem_nhds hHalf)
      have hNear : ∀ᶠ n : ℕ in atTop, dist (d n) h < ε := by
        filter_upwards [hvNear, hrNear] with n hn hr
        have htri := dist_triangle (d n) (v n) h
        linarith only [(hd n).2.2, hn, hr, htri]
      exact eventually_atTop.1 hNear
    exact ⟨d, fun n => ⟨(hd n).1, (hd n).2.1⟩, hdTendsto⟩
  have hLeft (h : CoalescingTilt μ) (v : ℕ → CoalescingTilt μ)
      (hvSide : ∀ n, (v n).val.1 < h.val.1)
      (hv : Tendsto v atTop (𝓝 h)) :
      Tendsto (fun n => L (v n)) atTop (𝓝 (L h)) ∧
      Tendsto (fun n => R (v n)) atTop (𝓝 (L h)) := by
    have hLower (n : ℕ) : L h ≤ R (v n) := hCross (v n) h (hvSide n)
    have hMiddle (n : ℕ) : R (v n) ≤ L (v n) := hWithin (v n)
    have hL : Tendsto (fun n => L (v n)) atTop (𝓝 (L h)) := by
      by_cases hh : h ∈ D
      · obtain ⟨d, hd, hdTendsto⟩ := hDiagonalLeft h v hvSide hv
        have hdSide (n : ℕ) : d n ∈ D ∧ (d n).val.1 < h.val.1 :=
          ⟨(hd n).1, (hd n).2.elim
            (fun heq => heq ▸ hvSide n)
            (fun hlt => hlt.trans (hvSide n))⟩
        have hFd : Tendsto (fun n => f (d n)) atTop (𝓝 (L h)) := by
          rw [(hAtSample h hh).1]
          exact (hSample h hh).1 d hdSide hdTendsto
        have hUpper (n : ℕ) : L (v n) ≤ f (d n) := by
          rcases (hd n).2 with heq | hlt
          · rw [heq, (hAtSample (v n) (heq ▸ (hd n).1)).1]
          · calc
              L (v n) ≤ R (d n) := hCross (d n) (v n) hlt
              _ = f (d n) := (hAtSample (d n) (hd n).1).2
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le
          tendsto_const_nhds hFd (fun n => le_trans (hLower n) (hMiddle n)) hUpper
      · rcases (hSequences h).2 hh with ⟨hLeftMem, _, _, _, _, _⟩
        have hUpper (m : ℕ) : ∀ᶠ n in atTop, L (v n) ≤ f (left h m) := by
          have hEventually : ∀ᶠ n in atTop, (left h m).val.1 < (v n).val.1 :=
            (hCoordinate h v hv).eventually (Ioi_mem_nhds (hLeftMem m).2)
          filter_upwards [hEventually] with n hn
          calc
            L (v n) ≤ R (left h m) := hCross (left h m) (v n) hn
            _ = f (left h m) := (hAtSample (left h m) (hLeftMem m).1).2
        exact tendsto_of_upper_brackets
          (fun m => f (left h m)) (fun n => L (v n)) (L h)
          (hFinite h).1 (fun m => by
            filter_upwards [hUpper m] with n hn
            exact ⟨le_trans (hLower n) (hMiddle n), hn⟩)
    have hR : Tendsto (fun n => R (v n)) atTop (𝓝 (L h)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hL hLower hMiddle
    exact ⟨hL, hR⟩
  have hRight (h : CoalescingTilt μ) (v : ℕ → CoalescingTilt μ)
      (hvSide : ∀ n, h.val.1 < (v n).val.1)
      (hv : Tendsto v atTop (𝓝 h)) :
      Tendsto (fun n => L (v n)) atTop (𝓝 (R h)) ∧
      Tendsto (fun n => R (v n)) atTop (𝓝 (R h)) := by
    have hUpper (n : ℕ) : L (v n) ≤ R h := hCross h (v n) (hvSide n)
    have hMiddle (n : ℕ) : R (v n) ≤ L (v n) := hWithin (v n)
    have hR : Tendsto (fun n => R (v n)) atTop (𝓝 (R h)) := by
      by_cases hh : h ∈ D
      · obtain ⟨d, hd, hdTendsto⟩ := hDiagonalRight h v hvSide hv
        have hdSide (n : ℕ) : d n ∈ D ∧ h.val.1 < (d n).val.1 :=
          ⟨(hd n).1, (hd n).2.elim
            (fun heq => heq ▸ hvSide n)
            (fun hlt => (hvSide n).trans hlt)⟩
        have hFd : Tendsto (fun n => f (d n)) atTop (𝓝 (R h)) := by
          rw [(hAtSample h hh).2]
          exact (hSample h hh).2 d hdSide hdTendsto
        have hLower (n : ℕ) : f (d n) ≤ R (v n) := by
          rcases (hd n).2 with heq | hlt
          · rw [heq, (hAtSample (v n) (heq ▸ (hd n).1)).2]
          · calc
              f (d n) = L (d n) := (hAtSample (d n) (hd n).1).1.symm
              _ ≤ R (v n) := hCross (v n) (d n) hlt
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le
          hFd tendsto_const_nhds hLower
          (fun n => le_trans (hMiddle n) (hUpper n))
      · rcases (hSequences h).2 hh with ⟨_, _, _, hRightMem, _, _⟩
        have hLower (m : ℕ) : ∀ᶠ n in atTop, f (right h m) ≤ R (v n) := by
          have hEventually : ∀ᶠ n in atTop, (v n).val.1 < (right h m).val.1 :=
            (hCoordinate h v hv).eventually (Iio_mem_nhds (hRightMem m).2)
          filter_upwards [hEventually] with n hn
          calc
            f (right h m) = L (right h m) :=
              (hAtSample (right h m) (hRightMem m).1).1.symm
            _ ≤ R (v n) := hCross (v n) (right h m) hn
        exact tendsto_of_lower_brackets
          (fun m => f (right h m)) (fun n => R (v n)) (R h)
          (hFinite h).2 (fun m => by
            filter_upwards [hLower m] with n hn
            exact ⟨hn, le_trans (hMiddle n) (hUpper n)⟩)
    have hL : Tendsto (fun n => L (v n)) atTop (𝓝 (R h)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        hR tendsto_const_nhds hMiddle hUpper
    exact ⟨hL, hR⟩
  exact ⟨by intro h v hvSide hv; exact hLeft h v hvSide hv,
    by intro h v hvSide hv; exact hRight h v hvSide hv⟩

end LPP.Busemann
