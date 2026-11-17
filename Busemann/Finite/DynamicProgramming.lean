/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.FiniteTiltedPotential
import Busemann.Finite.PotentialOrder
import LPP_Foundations.Model.LastPassage.Outgoing
import LPP_Foundations.Model.LastPassage.Inclusive
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! # Outgoing dynamic programming for the actual finite tilted potential -/

public section

open LPPDifferentiability

namespace LPP.Busemann

private theorem potential_real_le_iff
    (ω : Environment) (h : ℝ × ℝ) (x : Lattice) (n : ℤ)
    (hx : x.1 + x.2 ≤ n) (m : ℕ) (hlen : (n - (x.1 + x.2)).toNat = m) (r : ℝ) :
    (finiteTiltedPotential ω h x n).toReal ≤ r ↔
      ∀ k : Fin (m + 1), lastPassage ω x (k.val, m - k.val) +
        h.1 * (k.val : ℝ) + h.2 * ((m - k.val : ℕ) : ℝ) ≤ r := by
  subst m
  have hcoe := EReal.coe_toReal (finiteTiltedPotential_ne_top ω h x n hx)
    (finiteTiltedPotential_ne_bot ω h x n hx)
  have hiff := finiteTiltedPotential_le_coe_iff ω h x n hx r
  rw [← hcoe] at hiff
  simpa only [EReal.coe_le_coe_iff] using hiff

/-- At every active horizon, the real value of the actual finite potential is
the starting signed weight plus the larger tilted child value. This is the
finite outgoing recurrence behind JR1810.03580v3 (4.14). -/
theorem finiteTiltedPotential_toReal_outgoing
    (ω : Environment) (h : ℝ × ℝ) (x : Lattice) (n : ℤ) (hx : x.1 + x.2 < n) :
    (finiteTiltedPotential ω h x n).toReal = ω x +
      max (h.1 + (finiteTiltedPotential ω h (x + (1, 0)) n).toReal)
        (h.2 + (finiteTiltedPotential ω h (x + (0, 1)) n).toReal) := by
  let m : ℕ := (n - (x.1 + x.2) - 1).toNat
  let P : ℝ := (finiteTiltedPotential ω h x n).toReal
  let R : ℝ := (finiteTiltedPotential ω h (x + (1, 0)) n).toReal
  let U : ℝ := (finiteTiltedPotential ω h (x + (0, 1)) n).toReal
  change P = ω x + max (h.1 + R) (h.2 + U)
  have hxR : (x + (1, 0)).1 + (x + (1, 0)).2 ≤ n := by
    change x.1 + 1 + (x.2 + 0) ≤ n
    omega
  have hxU : (x + (0, 1)).1 + (x + (0, 1)).2 ≤ n := by
    change x.1 + 0 + (x.2 + 1) ≤ n
    omega
  have hlenP : (n - (x.1 + x.2)).toNat = m + 1 := by dsimp only [m]; omega
  have hlenR : (n - ((x + (1, 0)).1 + (x + (1, 0)).2)).toNat = m := by
    change (n - (x.1 + 1 + (x.2 + 0))).toNat = m
    dsimp only [m]
    omega
  have hlenU : (n - ((x + (0, 1)).1 + (x + (0, 1)).2)).toNat = m := by
    change (n - (x.1 + 0 + (x.2 + 1))).toNat = m
    dsimp only [m]
    omega
  have hparent : ∀ k : Fin (m + 1 + 1),
      lastPassage ω x (k.val, m + 1 - k.val) +
        h.1 * (k.val : ℝ) + h.2 * ((m + 1 - k.val : ℕ) : ℝ) ≤ P :=
    (potential_real_le_iff ω h x n hx.le (m + 1) hlenP P).mp le_rfl
  have hright : ∀ k : Fin (m + 1),
      lastPassage ω (x + (1, 0)) (k.val, m - k.val) +
        h.1 * (k.val : ℝ) + h.2 * ((m - k.val : ℕ) : ℝ) ≤ R :=
    (potential_real_le_iff ω h _ n hxR m hlenR R).mp le_rfl
  have hup : ∀ k : Fin (m + 1),
      lastPassage ω (x + (0, 1)) (k.val, m - k.val) +
        h.1 * (k.val : ℝ) + h.2 * ((m - k.val : ℕ) : ℝ) ≤ U :=
    (potential_real_le_iff ω h _ n hxU m hlenU U).mp le_rfl
  -- Bound each parent candidate by one of the two tilted child potentials.
  have hupper : P ≤ ω x + max (h.1 + R) (h.2 + U) := by
    apply (potential_real_le_iff ω h x n hx.le (m + 1) hlenP _).mpr
    intro k
    have hk : k.val ≤ m + 1 := by have := k.isLt; omega
    by_cases hkzero : k.val = 0
    · have hc := hup ⟨0, by omega⟩
      simp only [Nat.sub_zero, Nat.cast_zero, mul_zero, add_zero] at hc
      rw [hkzero, Nat.sub_zero, lastPassage_outgoing_vertical_succ]
      simp only [Nat.cast_zero, mul_zero, add_zero, Nat.cast_add, Nat.cast_one]
      have hmax := le_max_right (h.1 + R) (h.2 + U)
      linarith only [hc, hmax]
    · by_cases hkmax : k.val = m + 1
      · have hc := hright ⟨m, by omega⟩
        simp only [Nat.sub_self, Nat.cast_zero, mul_zero, add_zero] at hc
        rw [hkmax, Nat.sub_self, lastPassage_outgoing_horizontal_succ]
        simp only [Nat.cast_zero, mul_zero, add_zero, Nat.cast_add, Nat.cast_one]
        have hmax := le_max_left (h.1 + R) (h.2 + U)
        linarith only [hc, hmax]
      · have hkpred : k.val = k.val - 1 + 1 := by omega
        have hvpred : m + 1 - k.val = m - k.val + 1 := by omega
        have hrlen : m - (k.val - 1) = m + 1 - k.val := by omega
        have hrec := lastPassage_outgoing_succ_succ ω x (k.val - 1) (m - k.val)
        rw [← hkpred, ← hvpred] at hrec
        have hR := hright ⟨k.val - 1, by omega⟩
        rw [hrlen] at hR
        have hU := hup ⟨k.val, by omega⟩
        rw [hrec]
        rcases le_total
            (lastPassage ω (x + (1, 0)) (k.val - 1, m + 1 - k.val))
            (lastPassage ω (x + (0, 1)) (k.val, m - k.val)) with hle | hle
        · rw [max_eq_right hle]
          have hvcast : ((m + 1 - k.val : ℕ) : ℝ) = ((m - k.val : ℕ) : ℝ) + 1 := by
            exact_mod_cast hvpred
          rw [hvcast]
          have hmax := le_max_right (h.1 + R) (h.2 + U)
          linarith only [hU, hmax]
        · rw [max_eq_left hle]
          have hkcast : (k.val : ℝ) = ((k.val - 1 : ℕ) : ℝ) + 1 := by
            exact_mod_cast hkpred
          rw [hkcast]
          have hmax := le_max_left (h.1 + R) (h.2 + U)
          linarith only [hR, hmax]
  -- Conversely, prepend one step to each child candidate and bound it at the parent.
  have hrightLower : R ≤ P - ω x - h.1 := by
    apply (potential_real_le_iff ω h _ n hxR m hlenR _).mpr
    intro j
    have hj : j.val ≤ m := by have := j.isLt; omega
    have hsub : m + 1 - (j.val + 1) = m - j.val := by omega
    have hc := hparent ⟨j.val + 1, by omega⟩
    rw [hsub] at hc
    have hs := lastPassage_superadditive ω x (1, 0) (j.val, m - j.val)
    have hstep : ω x + lastPassage ω (x + (1, 0)) (j.val, m - j.val) ≤
        lastPassage ω x (j.val + 1, m - j.val) := by
      simpa only [lastPassage_horizontal_one, Prod.mk_add_mk, Nat.one_add, Nat.zero_add,
        Nat.cast_one, Nat.cast_zero] using hs
    simp only [Nat.cast_add, Nat.cast_one] at hc
    linarith only [hc, hstep]
  have hupLower : U ≤ P - ω x - h.2 := by
    apply (potential_real_le_iff ω h _ n hxU m hlenU _).mpr
    intro j
    have hj : j.val ≤ m := by have := j.isLt; omega
    have hsub : m + 1 - j.val = (m - j.val) + 1 := by omega
    have hc := hparent ⟨j.val, by omega⟩
    rw [hsub] at hc
    have hs := lastPassage_superadditive ω x (0, 1) (j.val, m - j.val)
    have hstep : ω x + lastPassage ω (x + (0, 1)) (j.val, m - j.val) ≤
        lastPassage ω x (j.val, (m - j.val) + 1) := by
      simpa only [lastPassage_vertical_one, Prod.mk_add_mk, Nat.one_add, Nat.zero_add,
        Nat.cast_one, Nat.cast_zero] using hs
    simp only [Nat.cast_add, Nat.cast_one] at hc
    linarith only [hc, hstep]
  apply le_antisymm hupper
  have hmaxBound : max (h.1 + R) (h.2 + U) ≤ P - ω x :=
    max_le (by linarith only [hrightLower]) (by linarith only [hupLower])
  linarith only [hmaxBound]

/-- The actual EReal finite potential obeys outgoing dynamic programming at
any active horizon, with arbitrary signed weights; see JR1810.03580v3 (4.14). -/
theorem finiteTiltedPotential_outgoing
    (ω : Environment) (h : ℝ × ℝ) (x : Lattice) (n : ℤ) (hx : x.1 + x.2 < n) :
    finiteTiltedPotential ω h x n = (ω x : EReal) +
      max ((h.1 : EReal) + finiteTiltedPotential ω h (x + (1, 0)) n)
        ((h.2 : EReal) + finiteTiltedPotential ω h (x + (0, 1)) n) := by
  have hxR : (x + (1, 0)).1 + (x + (1, 0)).2 ≤ n := by
    change x.1 + 1 + (x.2 + 0) ≤ n
    omega
  have hxU : (x + (0, 1)).1 + (x + (0, 1)).2 ≤ n := by
    change x.1 + 0 + (x.2 + 1) ≤ n
    omega
  have hP := EReal.coe_toReal (finiteTiltedPotential_ne_top ω h x n hx.le)
    (finiteTiltedPotential_ne_bot ω h x n hx.le)
  have hR := EReal.coe_toReal (finiteTiltedPotential_ne_top ω h _ n hxR)
    (finiteTiltedPotential_ne_bot ω h _ n hxR)
  have hU := EReal.coe_toReal (finiteTiltedPotential_ne_top ω h _ n hxU)
    (finiteTiltedPotential_ne_bot ω h _ n hxU)
  have hmax : ∀ a b : ℝ, ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) := by
    intro a b
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab, max_eq_right (EReal.coe_le_coe hab)]
    · rw [max_eq_left hba, max_eq_left (EReal.coe_le_coe hba)]
  have hcoe := congrArg (fun r : ℝ => (r : EReal))
    (finiteTiltedPotential_toReal_outgoing ω h x n hx)
  simpa only [EReal.coe_add, hmax, hP, hR, hU] using hcoe

end LPP.Busemann
