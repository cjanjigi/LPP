/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Analysis.RationalRateConsistency
public import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Existence of the rational extension of a natural rate

These are abstract conditional algebraic helpers. They construct a unique
function on nonnegative rational pairs from a naturally homogeneous
real-valued function on natural pairs. They do not define a shape or
establish any probabilistic limit.
-/

public section

open scoped NNRat

namespace LPPDifferentiability

/-- Every pair of nonnegative rationals has a positive common natural
 denominator, including the origin and the coordinate axes. -/
theorem nnrat_pair_exists_nat_div (q : ℚ≥0 × ℚ≥0) :
    ∃ d : ℕ, 0 < d ∧ ∃ a : ℕ × ℕ,
      q = ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) := by
  refine ⟨q.1.den * q.2.den, Nat.mul_pos q.1.den_pos q.2.den_pos,
    (q.1.num * q.2.den, q.2.num * q.1.den), ?_⟩
  apply Prod.ext
  · dsimp
    rw [Nat.cast_mul, Nat.cast_mul,
      mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr q.2.den_ne_zero),
      NNRat.num_div_den]
  · dsimp
    rw [Nat.cast_mul, Nat.cast_mul, mul_comm (q.1.den : ℚ≥0),
      mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr q.1.den_ne_zero),
      NNRat.num_div_den]

/-- Equality of two rational-pair representations gives equality of
 their signed real rates after positive division. -/
theorem natural_rate_eq_div_of_nnrat_pair_eq
    (g : (ℕ × ℕ) → ℝ)
    (hscale : ∀ (k : ℕ) (a : ℕ × ℕ), g (k • a) = (k : ℝ) * g a)
    (a b : ℕ × ℕ) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hrep : ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) =
      ((b.1 : ℚ≥0) / e, (b.2 : ℚ≥0) / e)) :
    g a / (d : ℝ) = g b / (e : ℝ) := by
  apply natural_rate_eq_div_of_smul_eq g hscale a b d e hd he
  have hd0 : (d : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have he0 : (e : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt he)
  apply Prod.ext
  · have h := (div_eq_div_iff hd0 he0).mp (congrArg Prod.fst hrep)
    have hn : a.1 * e = b.1 * d := by exact_mod_cast h
    simpa only [Prod.smul_fst, smul_eq_mul, mul_comm] using hn
  · have h := (div_eq_div_iff hd0 he0).mp (congrArg Prod.snd hrep)
    have hn : a.2 * e = b.2 * d := by exact_mod_cast h
    simpa only [Prod.smul_snd, smul_eq_mul, mul_comm] using hn

/-- A naturally homogeneous signed rate has exactly one function on the
 whole nonnegative rational quadrant with the indicated representation law.
 The zero premise records the natural rate convention (and follows already
 from scaling with scalar zero). No public function
 is defined by this existence proof. -/
theorem existsUnique_nnrat_rate_of_natural_homogeneous
    (g : (ℕ × ℕ) → ℝ) (_hzero : g 0 = 0)
    (hscale : ∀ (k : ℕ) (a : ℕ × ℕ), g (k • a) = (k : ℝ) * g a) :
    ∃! F : (ℚ≥0 × ℚ≥0) → ℝ,
      ∀ (d : ℕ), 0 < d → ∀ a : ℕ × ℕ,
        F ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) = g a / (d : ℝ) := by
  classical
  have hv : ∀ q : ℚ≥0 × ℚ≥0, ∃ v : ℝ,
      ∀ (d : ℕ), 0 < d → ∀ a : ℕ × ℕ,
        q = ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) → v = g a / (d : ℝ) := by
    intro q
    obtain ⟨e, he, b, hb⟩ := nnrat_pair_exists_nat_div q
    refine ⟨g b / (e : ℝ), ?_⟩
    intro d hd a ha
    exact natural_rate_eq_div_of_nnrat_pair_eq g hscale b a e d he hd (hb.symm.trans ha)
  let F : (ℚ≥0 × ℚ≥0) → ℝ := fun q => Classical.choose (hv q)
  have hF : ∀ (d : ℕ), 0 < d → ∀ a : ℕ × ℕ,
      F ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) = g a / (d : ℝ) := by
    intro d hd a
    exact Classical.choose_spec (hv _) d hd a rfl
  refine ⟨F, hF, ?_⟩
  intro H hH
  funext q
  obtain ⟨d, hd, a, ha⟩ := nnrat_pair_exists_nat_div q
  rw [ha, hH d hd a, hF d hd a]


/-- The representation law restricts to the given natural rate. -/
theorem nnrat_rate_natCast
    (g : (ℕ × ℕ) → ℝ) (F : (ℚ≥0 × ℚ≥0) → ℝ)
    (hF : ∀ (d : ℕ), 0 < d → ∀ a : ℕ × ℕ,
      F ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) = g a / (d : ℝ))
    (a : ℕ × ℕ) : F (a.1, a.2) = g a := by
  simpa only [Nat.cast_one, div_one] using hF 1 Nat.one_pos a

/-- The same characterized function has value zero at the origin. -/
theorem nnrat_rate_zero
    (g : (ℕ × ℕ) → ℝ) (hzero : g 0 = 0) (F : (ℚ≥0 × ℚ≥0) → ℝ)
    (hF : ∀ (d : ℕ), 0 < d → ∀ a : ℕ × ℕ,
      F ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) = g a / (d : ℝ)) :
    F 0 = 0 := by
  change F (0, 0) = 0
  simpa only [Prod.fst_zero, Prod.snd_zero, Nat.cast_zero, hzero] using
    nnrat_rate_natCast g F hF 0

/-- Multiplying a rational pair by a nonnegative rational scalar gives the
 natural numerator and positive-denominator representation used for scaling. -/
theorem nnrat_smul_nat_div (c : ℚ≥0) (a : ℕ × ℕ) (d : ℕ) :
    c • ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) =
      (((c.num • a).1 : ℚ≥0) / ((c.den * d : ℕ) : ℚ≥0),
        ((c.num • a).2 : ℚ≥0) / ((c.den * d : ℕ) : ℚ≥0)) := by
  apply Prod.ext
  · simp only [Prod.smul_fst, smul_eq_mul, Nat.cast_mul]
    conv_lhs => rw [← NNRat.num_div_den c]
    exact div_mul_div_comm _ _ _ _
  · simp only [Prod.smul_snd, smul_eq_mul, Nat.cast_mul]
    conv_lhs => rw [← NNRat.num_div_den c]
    exact div_mul_div_comm _ _ _ _

/-- The same characterized function is homogeneous for every nonnegative
 rational scalar, including zero, without any sign assumption on its values. -/
theorem nnrat_rate_smul
    (g : (ℕ × ℕ) → ℝ)
    (hscale : ∀ (k : ℕ) (a : ℕ × ℕ), g (k • a) = (k : ℝ) * g a)
    (F : (ℚ≥0 × ℚ≥0) → ℝ)
    (hF : ∀ (d : ℕ), 0 < d → ∀ a : ℕ × ℕ,
      F ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) = g a / (d : ℝ))
    (c : ℚ≥0) (q : ℚ≥0 × ℚ≥0) : F (c • q) = (c : ℝ) * F q := by
  obtain ⟨d, hd, a, ha⟩ := nnrat_pair_exists_nat_div q
  rw [ha, nnrat_smul_nat_div, hF (c.den * d) (Nat.mul_pos c.den_pos hd),
    hscale, hF d hd, Nat.cast_mul, NNRat.cast_def]
  exact (div_mul_div_comm _ _ _ _).symm

/-- Addition of two rational representations can use the product of their
 positive denominators. -/
theorem nnrat_nat_div_add (a b : ℕ × ℕ) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e) :
    ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) +
      ((b.1 : ℚ≥0) / e, (b.2 : ℚ≥0) / e) =
      ((((e • a + d • b).1 : ℕ) : ℚ≥0) / ((d * e : ℕ) : ℚ≥0),
        (((e • a + d • b).2 : ℕ) : ℚ≥0) / ((d * e : ℕ) : ℚ≥0)) := by
  have hd0 : (d : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have he0 : (e : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt he)
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Nat.cast_add, Nat.cast_mul]
    field_simp
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Nat.cast_add, Nat.cast_mul]
    field_simp

/-- Superadditivity passes to the same rational function characterized by
 positive natural denominator representations. -/
theorem nnrat_rate_superadditive
    (g : (ℕ × ℕ) → ℝ)
    (hscale : ∀ (k : ℕ) (a : ℕ × ℕ), g (k • a) = (k : ℝ) * g a)
    (hadd : ∀ a b : ℕ × ℕ, g a + g b ≤ g (a + b))
    (F : (ℚ≥0 × ℚ≥0) → ℝ)
    (hF : ∀ (d : ℕ), 0 < d → ∀ a : ℕ × ℕ,
      F ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) = g a / (d : ℝ))
    (q r : ℚ≥0 × ℚ≥0) : F q + F r ≤ F (q + r) := by
  obtain ⟨d, hd, a, ha⟩ := nnrat_pair_exists_nat_div q
  obtain ⟨e, he, b, hb⟩ := nnrat_pair_exists_nat_div r
  rw [ha, hb, nnrat_nat_div_add a b d e hd he,
    hF d hd, hF e he, hF (d * e) (Nat.mul_pos hd he)]
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have he0 : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt he)
  have h := natural_rate_add_div_le_of_superadditive g hadd
    (e • a) (d • b) (d * e) (Nat.mul_pos hd he)
  rw [hscale, hscale, Nat.cast_mul] at h
  have hleft : (e : ℝ) * g a / ((d : ℝ) * e) = g a / (d : ℝ) := by
    field_simp
  have hright : (d : ℝ) * g b / ((d : ℝ) * e) = g b / (e : ℝ) := by
    field_simp
  rwa [hleft, hright, ← Nat.cast_mul] at h


/-- The same characterized function inherits both exact axis formulas for
 an arbitrary signed real coefficient. -/
theorem nnrat_rate_axes
    (g : (ℕ × ℕ) → ℝ) (F : (ℚ≥0 × ℚ≥0) → ℝ)
    (hF : ∀ (d : ℕ), 0 < d → ∀ a : ℕ × ℕ,
      F ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) = g a / (d : ℝ))
    (m : ℝ) (hx : ∀ n : ℕ, g (n, 0) = m * n)
    (hy : ∀ n : ℕ, g (0, n) = m * n) :
    (∀ q : ℚ≥0, F (q, 0) = m * (q : ℝ)) ∧
      (∀ q : ℚ≥0, F (0, q) = m * (q : ℝ)) := by
  constructor
  · intro q
    have h := hF q.den q.den_pos (q.num, 0)
    simpa only [Prod.fst, Prod.snd, Nat.cast_zero, zero_div,
      NNRat.num_div_den, hx, NNRat.cast_def, mul_div_assoc] using h
  · intro q
    have h := hF q.den q.den_pos (0, q.num)
    simpa only [Prod.fst, Prod.snd, Nat.cast_zero, zero_div,
      NNRat.num_div_den, hy, NNRat.cast_def, mul_div_assoc] using h

/-- Signed linear lower and upper natural bounds hold for the same rational
 witness, by division by its positive common denominator. -/
theorem nnrat_rate_bounds
    (g : (ℕ × ℕ) → ℝ) (F : (ℚ≥0 × ℚ≥0) → ℝ)
    (hF : ∀ (d : ℕ), 0 < d → ∀ a : ℕ × ℕ,
      F ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) = g a / (d : ℝ))
    (m M : ℝ)
    (hlo : ∀ a : ℕ × ℕ, m * ((a.1 : ℝ) + a.2) ≤ g a)
    (hup : ∀ a : ℕ × ℕ, g a ≤ M * ((a.1 : ℝ) + a.2))
    (q : ℚ≥0 × ℚ≥0) :
    m * ((q.1 : ℝ) + q.2) ≤ F q ∧ F q ≤ M * ((q.1 : ℝ) + q.2) := by
  obtain ⟨d, hd, a, ha⟩ := nnrat_pair_exists_nat_div q
  rw [ha, hF d hd]
  simp only [NNRat.cast_div, NNRat.cast_natCast]
  have hdreal : 0 ≤ (d : ℝ) := (Nat.cast_pos.mpr hd).le
  constructor
  · calc
      m * ((a.1 : ℝ) / d + (a.2 : ℝ) / d) =
          (m * ((a.1 : ℝ) + a.2)) / d := by ring
      _ ≤ g a / (d : ℝ) := div_le_div_of_nonneg_right (hlo a) hdreal
  · calc
      g a / (d : ℝ) ≤ (M * ((a.1 : ℝ) + a.2)) / d :=
        div_le_div_of_nonneg_right (hup a) hdreal
      _ = M * ((a.1 : ℝ) / d + (a.2 : ℝ) / d) := by ring

end LPPDifferentiability
