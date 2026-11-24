/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.Attachments.Net
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-! The uniform cardinality bound used for the endpoint boxes. -/

public section

namespace LPPDifferentiability

/-- Scale the prescribed-net count to the common bound for both directions. -/
theorem IsLevelAttachmentNet.card_image_le_of_scale
    {a D s kappa A B : ℝ} {I : ℤ} {M : ℕ} {v : Fin (M + 1) → Lattice}
    (h : IsLevelAttachmentNet a (Nat.ceil (kappa * s)) I A B v)
    (ha : 0 < a) (ha1 : a < 1) (hD : 1 ≤ D) (hs : 0 < s) (hk : 0 < kappa)
    (hwidth : A ≤ B) (hcap : B - A ≤ 2 * D * s) :
    ((Finset.univ.image v).card : ℝ) ≤ 8 * D / (min a (1 - a) * kappa) + 2 := by
  classical
  let m := Nat.ceil (kappa * s)
  let θ := min a (1 - a)
  have ht : 0 < θ := lt_min ha (sub_pos.mpr ha1)
  have hmlo : kappa * s ≤ (m : ℝ) := Nat.le_ceil _
  have hmR : 0 < (m : ℝ) := (mul_pos hk hs).trans_le hmlo
  have hm : 0 < m := Nat.cast_pos.mp hmR
  have hden : 0 < θ * (m : ℝ) := mul_pos ht hmR
  have hden' : 0 < θ * kappa := mul_pos ht hk
  have hratio : 4 * (B - A) / (θ * (m : ℝ)) ≤ 8 * D / (θ * kappa) := by
    apply (div_le_div_iff₀ hden hden').mpr
    have hupper := mul_le_mul_of_nonneg_right hcap hden'.le
    have hlower := mul_le_mul_of_nonneg_left hmlo
      (mul_nonneg (by linarith only [hD] : 0 ≤ 8 * D) ht.le)
    nlinarith only [hupper, hlower]
  have himageNat : (Finset.univ.image v).card ≤ M + 1 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fin (M + 1)))) (f := v))
  have himage : ((Finset.univ.image v).card : ℝ) ≤ ((M + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr himageNat
  exact himage.trans ((h.card_bound ha ha1 hm hwidth).trans (add_le_add_left hratio 2))

end LPPDifferentiability
