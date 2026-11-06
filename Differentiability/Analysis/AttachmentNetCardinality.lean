/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.AttachmentScales
public import Differentiability.Model.LevelNet
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Attachment net cardinality

Uniform cardinal bounds for actual finite sets and the integer grids that
produce the source attachment nets.
-/

public section

namespace LPPDifferentiability

/-- The source count, the width bound, and `m ≥ κs` give a uniform bound for
the cardinality of an actual finite net. -/
theorem attachment_net_card_bound {α : Type*} [DecidableEq α]
    (D s kappa theta0 : ℝ) (m : ℕ) (w : ℝ) (N : Finset α)
    (hD : 1 ≤ D) (hs : 0 < s) (hkappa : 0 < kappa)
    (htheta0 : 0 < theta0) (hm : kappa * s ≤ (m : ℝ))
    (hw : w ≤ D * s + (m : ℝ))
    (hcard : (N.card : ℝ) < 4 * w / (theta0 * (m : ℝ))) :
    (N.card : ℝ) ≤ 4 * (D / kappa + 1) / theta0 := by
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le (mul_pos hkappa hs) hm
  have hratio : D * s / (m : ℝ) ≤ D / kappa := by
    apply (div_le_div_iff₀ hmpos hkappa).2
    have h := mul_le_mul_of_nonneg_left hm hDpos.le
    nlinarith [h]
  have hwidth : w / (m : ℝ) ≤ D * s / (m : ℝ) + 1 := by
    calc
      w / (m : ℝ) ≤ (D * s + (m : ℝ)) / (m : ℝ) :=
        div_le_div_of_nonneg_right hw hmpos.le
      _ = D * s / (m : ℝ) + 1 := by
        rw [add_div, div_self hmpos.ne']
  calc
    (N.card : ℝ) ≤ 4 * w / (theta0 * (m : ℝ)) := le_of_lt hcard
    _ = (4 / theta0) * (w / (m : ℝ)) := by
      field_simp [htheta0.ne', hmpos.ne']
    _ ≤ (4 / theta0) * (D / kappa + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hwidth, hratio]) (by positivity)
    _ = 4 * (D / kappa + 1) / theta0 := by ring

/-- The floor/ceiling grid on an integer level is an actual finite lattice
set. Its source count is strict, and its cardinality has the uniform bound. -/
theorem attachment_source_level_net_card_bound
    (D s kappa theta0 : ℝ) (m : ℕ) (A B c : ℝ) (I : ℤ)
    (hD : 1 ≤ D) (hs : 0 < s) (hkappa : 0 < kappa)
    (htheta0 : 0 < theta0) (hm : kappa * s ≤ (m : ℝ))
    (hspacing : 1 ≤ theta0 * (m : ℝ) / 4)
    (hwidth : 2 * theta0 * (m : ℝ) ≤ B - A)
    (hw : B - A ≤ D * s + (m : ℝ)) :
    ∃ (M : ℕ) (p q : ℤ) (N : Finset Lattice),
      1 ≤ M ∧ theta0 * (m : ℝ) / 4 ≤ (q : ℝ) ∧
      (q : ℝ) ≤ theta0 * (m : ℝ) / 2 ∧
      (M + 1 : ℝ) < (B - A) / (theta0 * (m : ℝ) / 4) ∧
      N = (Finset.range (M + 1)).image
        (fun j : ℕ =>
          (p + (j : ℤ) * q, I - (p + (j : ℤ) * q))) ∧
      (N.card : ℝ) < 4 * (B - A) / (theta0 * (m : ℝ)) ∧
      (N.card : ℝ) ≤ 4 * (D / kappa + 1) / theta0 := by
  classical
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le (mul_pos hkappa hs) hm
  let t : ℝ := theta0 * (m : ℝ) / 4
  have ht : 1 ≤ t := by simpa [t] using hspacing
  have hgridWidth : 8 * t ≤ B - A := by
    dsimp [t]
    nlinarith [hwidth]
  obtain ⟨M, p, q, hM, hqt, hqhi, _, _, _, _, _, _, hcount⟩ :=
    exists_integer_level_grid t A B c ht hgridWidth
  let site : ℕ → Lattice := fun j =>
    (p + (j : ℤ) * q, I - (p + (j : ℤ) * q))
  let net : Finset Lattice := (Finset.range (M + 1)).image site
  have hnetCard : net.card ≤ M + 1 := by
    calc
      net.card ≤ (Finset.range (M + 1)).card := by
        simpa [net] using
          (Finset.card_image_le (s := Finset.range (M + 1)) (f := site))
      _ = M + 1 := by simp
  have hnetCardReal : (net.card : ℝ) ≤ (M + 1 : ℝ) := by
    exact_mod_cast hnetCard
  have hcountReal : (M + 1 : ℝ) <
      4 * (B - A) / (theta0 * (m : ℝ)) := by
    calc
      (M + 1 : ℝ) < (B - A) / t := hcount
      _ = 4 * (B - A) / (theta0 * (m : ℝ)) := by
        dsimp [t]
        field_simp [ne_of_gt (mul_pos htheta0 hmpos)]
  have hnetStrict : (net.card : ℝ) <
      4 * (B - A) / (theta0 * (m : ℝ)) :=
    lt_of_le_of_lt hnetCardReal hcountReal
  have hnetBound := attachment_net_card_bound D s kappa theta0 m
    (B - A) net hD hs hkappa htheta0 hm hw hnetStrict
  refine ⟨M, p, q, net, hM, ?_, ?_, ?_, rfl, hnetStrict, hnetBound⟩
  · simpa [t] using hqt
  · dsimp [t] at hqhi
    linarith only [hqhi]
  · simpa [t] using hcount

/-- Two actual finite nets with the same source count bound have a product
family bounded by the square of the same uniform constant. -/
theorem attachment_net_pair_card_bound
    (D s kappa theta0 : ℝ) (m : ℕ) (w₁ w₂ : ℝ)
    (N₁ N₂ : Finset Lattice)
    (hD : 1 ≤ D) (hs : 0 < s) (hkappa : 0 < kappa)
    (htheta0 : 0 < theta0) (hm : kappa * s ≤ (m : ℝ))
    (hw₁ : w₁ ≤ D * s + (m : ℝ))
    (hw₂ : w₂ ≤ D * s + (m : ℝ))
    (hcard₁ : (N₁.card : ℝ) < 4 * w₁ / (theta0 * (m : ℝ)))
    (hcard₂ : (N₂.card : ℝ) < 4 * w₂ / (theta0 * (m : ℝ))) :
    ((N₁ ×ˢ N₂).card : ℝ) ≤ (4 * (D / kappa + 1) / theta0) ^ 2 := by
  have hN₁ := attachment_net_card_bound D s kappa theta0 m w₁ N₁
    hD hs hkappa htheta0 hm hw₁ hcard₁
  have hN₂ := attachment_net_card_bound D s kappa theta0 m w₂ N₂
    hD hs hkappa htheta0 hm hw₂ hcard₂
  calc
    ((N₁ ×ˢ N₂).card : ℝ) = (N₁.card : ℝ) * (N₂.card : ℝ) := by
      rw [Finset.card_product, Nat.cast_mul]
    _ ≤ (4 * (D / kappa + 1) / theta0) *
        (4 * (D / kappa + 1) / theta0) :=
      mul_le_mul hN₁ hN₂ (by positivity) (by positivity)
    _ = (4 * (D / kappa + 1) / theta0) ^ 2 := by ring

end LPPDifferentiability

end
