/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.ApproachesFaceInterval
public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import Busemann.Frozen.Definitions.LatticeEndpoint

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-! Deterministic reachability of fixed lattice sites along face-interval sequences. -/

@[expose] public section

open Filter LPPDifferentiability

namespace LPP.Busemann

/-- A sequence approaching an interior face interval eventually reaches any fixed site
and that site's indicated unit neighbor, as needed in GRS arXiv:1510.00860v2, (3.4), (3.8). -/
theorem eventually_reaches_of_approachesFaceInterval
    (v : ℕ → ℕ × ℕ) (left right : InteriorDirection)
    (hv : approachesFaceInterval v left right) (x : Lattice) (i : Fin 2) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      x ≤ latticeEndpoint (v n) ∧
        x + finiteEdgeStep i ≤ latticeEndpoint (v n) := by
  let s : ℕ → ℕ := fun n => (v n).1 + (v n).2
  let r : ℕ → ℝ := fun n => ((v n).1 : ℝ) / (s n : ℝ)
  let q : ℕ → ℝ := fun n => ((v n).2 : ℝ) / (s n : ℝ)

  -- The source assumption gives the exact escaping total and real ratio bounds.
  rcases hv with ⟨htotal_raw, hliminf_raw, hlimsup_raw⟩
  have htotal : Tendsto s atTop atTop := by
    simpa [s] using htotal_raw
  have hliminf : (left.1.1 : ℝ) ≤ liminf r atTop := by
    simpa [s, r] using hliminf_raw
  have hlimsup : limsup r atTop ≤ (right.1.1 : ℝ) := by
    simpa [s, r] using hlimsup_raw

  -- The ratio is bounded on its whole domain, including a zero total.
  have hr_nonneg (n : ℕ) : 0 ≤ r n := by
    by_cases hzero : s n = 0
    · have hsum_zero : (v n).1 + (v n).2 = 0 := by
        simpa [s] using hzero
      have hfirst_zero : (v n).1 = 0 := Nat.eq_zero_of_add_eq_zero_right hsum_zero
      simp [r, hzero, hfirst_zero]
    · have htotal_pos : 0 < s n := Nat.pos_of_ne_zero hzero
      have htotal_pos_real : (0 : ℝ) < (s n : ℝ) := by exact_mod_cast htotal_pos
      exact div_nonneg (Nat.cast_nonneg _) (le_of_lt htotal_pos_real)
  have hr_le_one (n : ℕ) : r n ≤ 1 := by
    by_cases hzero : s n = 0
    · have hsum_zero : (v n).1 + (v n).2 = 0 := by
        simpa [s] using hzero
      have hfirst_zero : (v n).1 = 0 := Nat.eq_zero_of_add_eq_zero_right hsum_zero
      simp [r, hzero, hfirst_zero]
    · have htotal_pos : 0 < s n := Nat.pos_of_ne_zero hzero
      have htotal_pos_real : (0 : ℝ) < (s n : ℝ) := by exact_mod_cast htotal_pos
      have hfirst_le : (v n).1 ≤ s n := by simp [s]
      have hfirst_le_real : ((v n).1 : ℝ) ≤ (s n : ℝ) := by
        exact_mod_cast hfirst_le
      exact (div_le_iff₀ htotal_pos_real).2 (by simpa using hfirst_le_real)
  have hr_bdd_below : IsBoundedUnder (· ≥ ·) atTop r :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hr_nonneg)
  have hr_bdd_above : IsBoundedUnder (· ≤ ·) atTop r :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hr_le_one)

  -- Positive endpoint coordinates leave strict room on both sides of the ratios.
  let a : ℝ := left.1.1 / 2
  let b : ℝ := (1 + right.1.1) / 2
  have hleft_first_pos : (0 : ℝ) < (left.1.1 : ℝ) := by
    exact_mod_cast left.2.1
  have hright_second_pos : (0 : ℝ) < (right.1.2 : ℝ) := by
    exact_mod_cast right.2.2.1
  have hright_sum : (right.1.1 : ℝ) + (right.1.2 : ℝ) = 1 := right.2.2.2
  have ha : 0 < a := by
    dsimp [a]
    linarith [hleft_first_pos]
  have hleft_a : a < left.1.1 := by
    dsimp [a]
    linarith [hleft_first_pos]
  have hright_lt_one : (right.1.1 : ℝ) < 1 := by
    linarith [hright_second_pos, hright_sum]
  have hright_b : (right.1.1 : ℝ) < b := by
    dsimp [b]
    linarith [hright_lt_one]
  have hb : b < 1 := by
    dsimp [b]
    linarith [hright_lt_one]
  have hone_sub_b : 0 < 1 - b := by linarith
  have ha_liminf : a < liminf r atTop := lt_of_lt_of_le hleft_a hliminf
  have hlimsup_b : limsup r atTop < b := lt_of_le_of_lt hlimsup hright_b
  have hratio_lower : ∀ᶠ n : ℕ in atTop, a < r n :=
    eventually_lt_of_lt_liminf ha_liminf hr_bdd_below
  have hratio_upper : ∀ᶠ n : ℕ in atTop, r n < b :=
    eventually_lt_of_limsup_lt hlimsup_b hr_bdd_above
  have hratio_strict : ∀ᶠ n : ℕ in atTop, a < r n ∧ r n < b :=
    hratio_lower.and hratio_upper

  -- Once the total is positive, the two normalized coordinates sum to one.
  have htotal_pos : ∀ᶠ n : ℕ in atTop, 0 < s n := by
    filter_upwards [Filter.tendsto_atTop.1 htotal 1] with n hn
    exact lt_of_lt_of_le (by decide) hn
  have hsecond_ratio (n : ℕ) (hn : 0 < s n) : q n = 1 - r n := by
    have htotal_pos_real : (0 : ℝ) < (s n : ℝ) := by exact_mod_cast hn
    have htotal_ne_real : (s n : ℝ) ≠ 0 := ne_of_gt htotal_pos_real
    have hsum_cast : (s n : ℝ) = ((v n).1 : ℝ) + ((v n).2 : ℝ) := by
      simp [s]
    dsimp [q, r]
    field_simp [htotal_ne_real]
    rw [hsum_cast]
    ring
  have hsecond_lower : ∀ᶠ n : ℕ in atTop, 1 - b < q n := by
    filter_upwards [hratio_strict, htotal_pos] with n hratio hn
    rw [hsecond_ratio n hn]
    linarith only [hratio.2]

  -- A positive fraction of an escaping total forces its numerator to escape.
  have hcoordinate_escape
      (coordinate : ℕ → ℕ) (fraction : ℕ → ℝ) (c : ℝ)
      (hc : 0 < c) (hfrac : ∀ᶠ n : ℕ in atTop, c < fraction n)
      (hfrac_eq : ∀ᶠ n : ℕ in atTop,
        fraction n = ((coordinate n : ℝ) / (s n : ℝ))) :
      Tendsto coordinate atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro K
    obtain ⟨M, hM⟩ := exists_nat_gt ((K : ℝ) / c)
    have hKM : (K : ℝ) < c * (M : ℝ) := by
      have hKDiv := (div_lt_iff₀ hc).mp hM
      simpa only [mul_comm] using hKDiv
    have htotal_large : ∀ᶠ n : ℕ in atTop, M ≤ s n :=
      Filter.tendsto_atTop.1 htotal M
    filter_upwards [htotal_large, htotal_pos, hfrac, hfrac_eq]
      with n hMtotal hstotal_pos hfrac_n heq
    have hMtotal_real : (M : ℝ) ≤ (s n : ℝ) := by exact_mod_cast hMtotal
    have hcoord_real : c * (s n : ℝ) < (coordinate n : ℝ) := by
      rw [heq] at hfrac_n
      exact (lt_div_iff₀ (by exact_mod_cast hstotal_pos : (0 : ℝ) < (s n : ℝ))).mp hfrac_n
    have hproduct : c * (M : ℝ) ≤ c * (s n : ℝ) :=
      mul_le_mul_of_nonneg_left hMtotal_real (le_of_lt hc)
    have hKcoord : (K : ℝ) < (coordinate n : ℝ) :=
      lt_trans hKM (lt_of_le_of_lt hproduct hcoord_real)
    exact_mod_cast hKcoord.le

  have hr_eq : ∀ᶠ n : ℕ in atTop,
      r n = ((v n).1 : ℝ) / (s n : ℝ) :=
    Eventually.of_forall fun _ => rfl
  have hfirst_tendsto : Tendsto (fun n => (v n).1) atTop atTop :=
    hcoordinate_escape (fun n => (v n).1) r a ha hratio_lower hr_eq
  have hq_eq : ∀ᶠ n : ℕ in atTop,
      q n = ((v n).2 : ℝ) / (s n : ℝ) :=
    Eventually.of_forall fun _ => rfl
  have hsecond_tendsto : Tendsto (fun n => (v n).2) atTop atTop :=
    hcoordinate_escape (fun n => (v n).2) q (1 - b) hone_sub_b hsecond_lower hq_eq

  -- Coordinate escape places both fixed lattice points below every late endpoint.
  have hfirst_int : Tendsto (fun n => ((v n).1 : ℤ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop).comp hfirst_tendsto
  have hsecond_int : Tendsto (fun n => ((v n).2 : ℤ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop).comp hsecond_tendsto
  have hx_first : ∀ᶠ n : ℕ in atTop, x.1 ≤ ((v n).1 : ℤ) :=
    Filter.tendsto_atTop.1 hfirst_int x.1
  have hx_second : ∀ᶠ n : ℕ in atTop, x.2 ≤ ((v n).2 : ℤ) :=
    Filter.tendsto_atTop.1 hsecond_int x.2
  have hx_reached : ∀ᶠ n : ℕ in atTop, x ≤ latticeEndpoint (v n) := by
    filter_upwards [hx_first, hx_second] with n hfirst hsecond
    change x.1 ≤ ((v n).1 : ℤ) ∧ x.2 ≤ ((v n).2 : ℤ)
    exact ⟨hfirst, hsecond⟩
  have hneighbor_first : ∀ᶠ n : ℕ in atTop,
      (x + finiteEdgeStep i).1 ≤ ((v n).1 : ℤ) :=
    Filter.tendsto_atTop.1 hfirst_int (x + finiteEdgeStep i).1
  have hneighbor_second : ∀ᶠ n : ℕ in atTop,
      (x + finiteEdgeStep i).2 ≤ ((v n).2 : ℤ) :=
    Filter.tendsto_atTop.1 hsecond_int (x + finiteEdgeStep i).2
  have hneighbor_reached : ∀ᶠ n : ℕ in atTop,
      x + finiteEdgeStep i ≤ latticeEndpoint (v n) := by
    filter_upwards [hneighbor_first, hneighbor_second] with n hfirst hsecond
    change (x + finiteEdgeStep i).1 ≤ ((v n).1 : ℤ) ∧
      (x + finiteEdgeStep i).2 ≤ ((v n).2 : ℤ)
    exact ⟨hfirst, hsecond⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hx_reached.and hneighbor_reached)
  exact ⟨N, fun n hn => hN n hn⟩

end LPP.Busemann
