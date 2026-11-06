/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Limits along finitely many residue classes

The deterministic interpolation is step (2.2) in the proof of Liggett (1985),
Theorem 1.10, between equation (2.8) and the resulting upper bound.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- Eventual bounds on all residue classes give an eventual bound on the whole
sequence. The initial quotient indices may be discarded. -/
theorem eventually_lt_of_residue_eventually_lt {u : ℕ → ℝ} {k : ℕ}
    (hk : 0 < k) {c : ℝ}
    (h : ∀ j < k, ∀ᶠ q : ℕ in atTop, u (q * k + j) < c) :
    ∀ᶠ n : ℕ in atTop, u n < c := by
  have hall : ∀ᶠ q : ℕ in atTop, ∀ j ∈ Finset.range k, u (q * k + j) < c := by
    apply (eventually_all_finset (Finset.range k)).2
    intro j hj
    exact h j (Finset.mem_range.mp hj)
  have hdiv := (Nat.tendsto_div_const_atTop (Nat.ne_of_gt hk)).eventually hall
  filter_upwards [hdiv] with n hn
  have hn' := hn (n % k) (Finset.mem_range.mpr (Nat.mod_lt n hk))
  rw [Nat.mul_comm (n / k) k, Nat.div_add_mod] at hn'
  exact hn'

/-- A common eventual upper bound along every residue class controls the
actual extended-real upper limit, without a lower bound on the sequence. -/
theorem limsup_coe_le_of_residue_eventually_lt {u : ℕ → ℝ} {k : ℕ}
    (hk : 0 < k) {v : ℝ}
    (h : ∀ c : ℝ, v < c → ∀ j < k,
      ∀ᶠ q : ℕ in atTop, u (q * k + j) < c) :
    limsup (fun n => (u n : EReal)) atTop ≤ (v : EReal) := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro c hc
  have hc' : v < c := EReal.coe_lt_coe_iff.mp hc
  exact limsup_le_of_le (by isBoundedDefault)
    ((eventually_lt_of_residue_eventually_lt hk (h c hc')).mono
      (fun n hn => EReal.coe_le_coe_iff.mpr hn.le))

/-- Changing the denominator from the block index to the whole interval
length gives the factor `1 / k`. This applies to signed numerators. -/
theorem tendsto_div_mul_add_of_tendsto_div_nat {f : ℕ → ℝ} {U : ℝ}
    (hf : Tendsto (fun q : ℕ => f q / (q : ℝ)) atTop (𝓝 U))
    {k : ℕ} (hk : 0 < k) (j : ℕ) :
    Tendsto (fun q : ℕ => f q / ((q * k + j : ℕ) : ℝ))
      atTop (𝓝 (U / (k : ℝ))) := by
  have hkreal : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hratio : Tendsto (fun q : ℕ => (q : ℝ) / ((q * k + j : ℕ) : ℝ))
      atTop (𝓝 (1 / (k : ℝ))) := by
    simpa only [zero_add, add_zero, one_mul, mul_one, Nat.cast_add, Nat.cast_mul,
      mul_comm, add_comm]
      using (tendsto_add_mul_div_add_mul_atTop_nhds (0 : ℝ) (j : ℝ) 1 hkreal)
  have hprod : Tendsto
      (fun q : ℕ => (f q / (q : ℝ)) * ((q : ℝ) / ((q * k + j : ℕ) : ℝ)))
      atTop (𝓝 (U / (k : ℝ))) := by
    simpa only [mul_one_div] using hf.mul hratio
  apply hprod.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with q hq
  have hqreal : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  field_simp [hqreal]

end LPPDifferentiability
