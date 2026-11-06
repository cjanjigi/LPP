/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Analysis.CenteredSuperadditive
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Lower limits from convergent block comparisons

These deterministic comparison lemmas are conditional on the displayed
limits and comparisons. They do not assert those limits for a stochastic
array. Extended reals retain the lower-limit statement even when no finite
upper bound holds pointwise.
-/

public section

open Filter Set
open scoped Topology

namespace LPPDifferentiability

/-- An eventually dominated convergent real comparison gives an extended-real
lower bound on the original sequence. -/
theorem le_liminf_ereal_of_tendsto_eventually_le {a b : ℕ → ℝ} {c : ℝ}
    (ha : Tendsto a atTop (𝓝 c)) (hab : ∀ᶠ n in atTop, a n ≤ b n) :
    (c : EReal) ≤ liminf (fun n => (b n : EReal)) atTop := by
  have he : Tendsto (fun n => (a n : EReal)) atTop (𝓝 (c : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp ha
  rw [← he.liminf_eq]
  exact liminf_le_liminf (hab.mono fun n hn => EReal.coe_le_coe hn)

/-- The same lower comparison can be taken over a bounded, nonempty set of
finite real rates. The boundedness is needed to identify its real supremum. -/
theorem coe_sSup_le_liminf_ereal {s : Set ℝ} (hne : s.Nonempty) (hbdd : BddAbove s)
    {b : ℕ → ℝ}
    (h : ∀ c ∈ s, (c : EReal) ≤ liminf (fun n => (b n : EReal)) atTop) :
    ((sSup s : ℝ) : EReal) ≤ liminf (fun n => (b n : EReal)) atTop := by
  generalize hL : liminf (fun n => (b n : EReal)) atTop = L at h ⊢
  induction L using EReal.rec with
  | bot =>
      obtain ⟨c, hc⟩ := hne
      exact False.elim ((not_le_of_gt (EReal.bot_lt_coe c)) (h c hc))
  | coe r =>
      exact EReal.coe_le_coe ((csSup_le_iff hbdd hne).mpr fun c hc => EReal.coe_le_coe_iff.mp (h c hc))
  | top => exact le_top


/-- The product of the covered fraction and per-length bilateral block mean
is exactly the raw block sum divided by the full centered interval length. -/
theorem block_average_scale_eq (S : ℝ) (r k N : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hN : 0 < N) :
    ((((r * k : ℕ) : ℝ) / (N : ℝ)) * (S / (2 * (r : ℝ)) / (k : ℝ))) =
      S / (2 * (N : ℝ)) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

end LPPDifferentiability
