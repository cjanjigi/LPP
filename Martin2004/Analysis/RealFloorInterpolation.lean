/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.PositiveQuadrantDensity
public import Martin2004.Analysis.RationalPassageNormalization
import Mathlib.Tactic

/-! # Interpolation of monotone floor means

These sequence lemmas use positive rational brackets and continuity only in
the interior. Signed sequences are made monotone by subtracting their linear
mean, which is restored using the floor length.
-/

public section

open Filter
open scoped NNRat NNReal Topology

namespace LPPDifferentiability

set_option quotPrecheck false in
local notation "ratInterior" =>
  (fun q : NNRatPairInterior =>
    (Subtype.mk (nnratPairToQuadrant q.val)
      (And.intro (NNRat.cast_pos.mpr q.property.1)
        (NNRat.cast_pos.mpr q.property.2)) : QuadrantInterior))

/-- A monotone lattice sequence with rational floor limits has the limit of
any continuous agreeing interior extension. This is a conditional helper. -/
theorem tendsto_monotone_floor_of_rational_limits
    (B : (ℕ × ℕ) → ℝ) (hmono : Monotone B)
    (F : (ℚ≥0 × ℚ≥0) → ℝ) (G : QuadrantInterior → ℝ)
    (hG : Continuous G)
    (hagrees : ∀ q : NNRatPairInterior, G (ratInterior q) = F q.val)
    (hlim : ∀ q : NNRatPairInterior, Tendsto (fun n : ℕ =>
      B (⌊(n : ℝ) * (q.val.1 : ℝ)⌋₊, ⌊(n : ℝ) * (q.val.2 : ℝ)⌋₊) /
        (n : ℝ)) atTop (𝓝 (F q.val)))
    (x : QuadrantInterior) :
    Tendsto (fun n : ℕ =>
      B (⌊(n : ℝ) * (x.val.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.val.2 : ℝ)⌋₊) /
        (n : ℝ)) atTop (𝓝 (G x)) := by
  obtain ⟨l, u, hbracket, hl, hu⟩ := exists_positive_rational_bracketing_sequences x
  have happrox (q : ℕ → NNRatPairInterior)
      (hq : Tendsto (fun j => nnratPairToQuadrant (q j).val) atTop (𝓝 x.val)) :
      Tendsto (fun j => F (q j).val) atTop (𝓝 (G x)) := by
    have hqi : Tendsto (fun j => ratInterior (q j)) atTop (𝓝 x) :=
      tendsto_subtype_rng.mpr hq
    have ht := (hG.tendsto x).comp hqi
    simpa only [Function.comp_def, hagrees] using ht
  have hlow := happrox l hl
  have hupp := happrox u hu
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨j, hj⟩ := (hlow.eventually_const_lt ha).exists
    filter_upwards [(hlim (l j)).eventually_const_lt hj] with n hn
    apply hn.trans_le
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    apply hmono
    exact ⟨Nat.floor_mono (mul_le_mul_of_nonneg_left (hbracket j).1.1
        (Nat.cast_nonneg n)),
      Nat.floor_mono (mul_le_mul_of_nonneg_left (hbracket j).1.2
        (Nat.cast_nonneg n))⟩
  · intro a ha
    obtain ⟨j, hj⟩ := (hupp.eventually_lt_const ha).exists
    filter_upwards [(hlim (u j)).eventually_lt_const hj] with n hn
    apply lt_of_le_of_lt _ hn
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    apply hmono
    exact ⟨Nat.floor_mono (mul_le_mul_of_nonneg_left (hbracket j).2.1
        (Nat.cast_nonneg n)),
      Nat.floor_mono (mul_le_mul_of_nonneg_left (hbracket j).2.2
        (Nat.cast_nonneg n))⟩

/-- Subtracting a signed linear mean allows monotone interpolation; restoring
the normalized floor length gives the original signed limit. -/
theorem tendsto_corrected_floor_of_rational_limits
    (E : (ℕ × ℕ) → ℝ) (m : ℝ)
    (hmono : Monotone (fun z : ℕ × ℕ => E z - ((z.1 + z.2 : ℕ) : ℝ) * m))
    (F : (ℚ≥0 × ℚ≥0) → ℝ) (G : QuadrantInterior → ℝ)
    (hG : Continuous G)
    (hagrees : ∀ q : NNRatPairInterior, G (ratInterior q) = F q.val)
    (hlim : ∀ q : ℚ≥0 × ℚ≥0, Tendsto (fun n : ℕ =>
      E (⌊(n : ℝ) * (q.1 : ℝ)⌋₊, ⌊(n : ℝ) * (q.2 : ℝ)⌋₊) /
        (n : ℝ)) atTop (𝓝 (F q)))
    (x : QuadrantInterior) :
    Tendsto (fun n : ℕ =>
      E (⌊(n : ℝ) * (x.val.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.val.2 : ℝ)⌋₊) /
        (n : ℝ)) atTop (𝓝 (G x)) := by
  let B : (ℕ × ℕ) → ℝ := fun z => E z - ((z.1 + z.2 : ℕ) : ℝ) * m
  let H : (ℚ≥0 × ℚ≥0) → ℝ := fun q => F q - ((q.1 : ℝ) + q.2) * m
  let J : QuadrantInterior → ℝ := fun y => G y - ((y.val.1 : ℝ) + y.val.2) * m
  have hJ : Continuous J := by dsimp [J]; fun_prop
  have hJH : ∀ q : NNRatPairInterior, J (ratInterior q) = H q.val := by
    intro q
    dsimp [J, H]
    rw [hagrees]
    simp only [NNRat.cast_def, NNReal.coe_div, NNReal.coe_natCast]
  have hBlim (q : NNRatPairInterior) : Tendsto (fun n : ℕ =>
      B (⌊(n : ℝ) * (q.val.1 : ℝ)⌋₊, ⌊(n : ℝ) * (q.val.2 : ℝ)⌋₊) /
        (n : ℝ)) atTop (𝓝 (H q.val)) := by
    have hlength := tendsto_floor_pair_length (q.val.1 : ℝ) (q.val.2 : ℝ)
      (NNRat.cast_nonneg _) (NNRat.cast_nonneg _)
    convert (hlim q.val).sub (hlength.mul_const m) using 1
    funext n
    dsimp [B]
    ring
  have hB := tendsto_monotone_floor_of_rational_limits B hmono H J hJ hJH hBlim x
  have hlength := tendsto_floor_pair_length (x.val.1 : ℝ) (x.val.2 : ℝ)
    x.val.1.property x.val.2.property
  have hsum := hB.add (hlength.mul_const m)
  have hvalue : J x + ((x.val.1 : ℝ) + x.val.2) * m = G x := by
    dsimp [J]
    ring
  rw [hvalue] at hsum
  convert hsum using 1
  funext n
  dsimp [B]
  ring

end LPPDifferentiability
