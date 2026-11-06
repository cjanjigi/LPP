/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Binomial logarithms along integer rays

The logarithmic binomial coefficient divided by the ray index converges to
its entropy expression. The proof retains the Stirling calculation invoked
in the bounded-boundary argument (Martin (2004), proof of Lemma 3.2).
Both coordinate axes are included.
-/

@[expose] public section

open Filter Real
open scoped Topology

namespace LPPDifferentiability

private theorem factorial_log_normalized (c : ℕ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => log ((n * c).factorial : ℝ) / n - (c : ℝ) * log n)
      atTop (𝓝 ((c : ℝ) * log c - c)) := by
  have hnat : Tendsto (fun n : ℕ => n * c) atTop atTop :=
    tendsto_id.atTop_mul_const' hc
  have hreal : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hs := ((Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp
    (Stirling.tendsto_stirlingSeq_sqrt_pi.comp hnat)).div_atTop hreal
  have hl : Tendsto (fun n : ℕ => log (n : ℝ) / n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hreal
  have hconst : Tendsto (fun n : ℕ => log (2 * (c : ℝ)) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hreal
  have hr := hs.add ((hl.add hconst).const_mul (1 / 2 : ℝ))
  have hlimit := hr.add (tendsto_const_nhds (x := (c : ℝ) * log c - c))
  simp only [zero_add, mul_zero] at hlimit
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hc' : (c : ℝ) ≠ 0 := by positivity
  dsimp only [Function.comp_apply]
  rw [Stirling.log_stirlingSeq_formula]
  simp only [Nat.cast_mul]
  rw [Real.log_div (mul_ne_zero hn' hc') (Real.exp_ne_zero 1), Real.log_exp,
    Real.log_mul hn' hc']
  have hlog : log (2 * ((n : ℝ) * c)) = log (n : ℝ) + log (2 * (c : ℝ)) := by
    rw [show 2 * ((n : ℝ) * c) = (n : ℝ) * (2 * c) by ring,
      Real.log_mul hn' (by positivity)]
  rw [hlog]
  field_simp
  ring

private theorem log_choose_add (i j : ℕ) :
    log ((i + j).choose j : ℝ) =
      log ((i + j).factorial : ℝ) - log (i.factorial : ℝ) - log (j.factorial : ℝ) := by
  have h := congrArg (fun k : ℕ => log (k : ℝ))
    (Nat.add_choose_mul_factorial_mul_factorial i j)
  have hchoose : ((i + j).choose j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : j ≤ i + j)).ne'
  have hi : (i.factorial : ℝ) ≠ 0 := by positivity
  have hj : (j.factorial : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_mul, Real.log_mul (mul_ne_zero hchoose hi) hj,
    Real.log_mul hchoose hi] at h
  linarith

/-- The integer-ray binomial logarithm has the entropy limit given by Stirling's formula,
including both coordinate axes. -/
theorem tendsto_log_choose_mul_div (a b : ℕ) :
    Tendsto (fun n : ℕ => log ((n * (a + b)).choose (n * a) : ℝ) / n)
      atTop (𝓝 (((a + b : ℕ) : ℝ) * log (a + b : ℕ) -
        (a : ℝ) * log a - (b : ℝ) * log b)) := by
  rcases eq_or_lt_of_le (Nat.zero_le a) with rfl | ha
  · simp
  rcases eq_or_lt_of_le (Nat.zero_le b) with rfl | hb
  · simp
  have h := ((factorial_log_normalized (a + b) (by omega)).sub
    (factorial_log_normalized a ha)).sub (factorial_log_normalized b hb)
  have heq : (((a + b : ℕ) : ℝ) * log (a + b : ℕ) - (a + b : ℕ) -
      ((a : ℝ) * log a - a) - ((b : ℝ) * log b - b)) =
      ((a + b : ℕ) : ℝ) * log (a + b : ℕ) -
        (a : ℝ) * log a - (b : ℝ) * log b := by
    push_cast
    ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [] with n
  rw [show n * (a + b) = n * b + n * a by ring, log_choose_add]
  simp only [Nat.cast_add]
  ring

/-- An eventual upper bound with any positive error above the exact entropy rate. -/
theorem eventually_log_choose_mul_le (a b : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      log ((n * (a + b)).choose (n * a) : ℝ) ≤
        (n : ℝ) * (((a + b : ℕ) : ℝ) * log (a + b : ℕ) -
          (a : ℝ) * log a - (b : ℝ) * log b + ε) := by
  have h := (tendsto_log_choose_mul_div a b).eventually
    (eventually_lt_nhds (lt_add_of_pos_right _ hε))
  filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  simpa only [mul_comm] using ((div_lt_iff₀ hn').mp hn).le

end LPPDifferentiability
