/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
import ProbabilityBasics.Combinatorics.IntegerRectangles
import ProbabilityBasics.Probability.InvariantIterates
import Mathlib.Tactic

/-! Prefix rectangle averages of a jointly invariant function. -/

public section

open Filter MeasureTheory
open scoped BigOperators Topology

namespace ProbabilityBasics

/-- A function invariant almost everywhere under both positive coordinate
shifts has prefix-rectangle averages converging to its value times the
rectangle area factor. This is the invariant-term step in Krengel,
*Ergodic Theorems*, §6.2, Theorem 2.8. -/
theorem ae_tendsto_prefix_rectangle_of_unit_invariant
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : (ℤ × ℤ) → Ω → Ω)
    (hzero : ∀ s, T 0 s = s)
    (hadd : ∀ z w s, T (z + w) s = T z (T w s))
    (hT : ∀ z, MeasurePreserving (T z) μ μ)
    (g : Ω → ℝ)
    (hinv : ∀ i : Fin 2, ∀ᵐ s ∂μ,
      g (T (if i = 0 then (1, 0) else (0, 1)) s) = g s)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) :
    let R : ℕ → Finset (ℤ × ℤ) := fun n =>
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
        (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
    ∀ᵐ s ∂μ, Tendsto (fun n : ℕ =>
      (∑ z ∈ R n, g (T z s)) / (n : ℝ)^2)
      atTop (𝓝 (b 0 * b 1 * g s)) := by
  let R : ℕ → Finset (ℤ × ℤ) := fun n =>
    (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
  let A : ℕ → ℕ := fun n => ⌊(n : ℝ) * b 0⌋₊
  let B : ℕ → ℕ := fun n => ⌊(n : ℝ) * b 1⌋₊
  change ∀ᵐ s ∂μ, Tendsto (fun n : ℕ =>
    (∑ z ∈ R n, g (T z s)) / (n : ℝ)^2)
    atTop (𝓝 (b 0 * b 1 * g s))

  -- Forward iterates preserve the almost-everywhere unit-shift identity.
  have hInvariant0 : ∀ᵐ s ∂μ, g (T (1, 0) s) = g s := by
    simpa using hinv 0
  have hInvariant1 : ∀ᵐ s ∂μ, g (T (0, 1) s) = g s := by
    simpa using hinv 1

  have hIterate0 (n : ℕ) (s : Ω) :
      ((fun t => T (1, 0) t)^[n]) s = T ((n : ℤ), 0) s := by
    induction n with
    | zero => exact (hzero s).symm
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        have hpair : ((1 : ℤ), (0 : ℤ)) + ((n : ℤ), (0 : ℤ)) =
            (((n + 1 : ℕ) : ℤ), (0 : ℤ)) := by
          ext <;> simp [Nat.cast_succ, add_comm]
        calc
          T (1, 0) (T ((n : ℤ), 0) s) =
              T (((1 : ℤ), 0) + ((n : ℤ), 0)) s := (hadd (1, 0) ((n : ℤ), 0) s).symm
          _ = T (((n + 1 : ℕ) : ℤ), 0) s := by
            exact congrArg (fun z : ℤ × ℤ => T z s) hpair

  have hIterate1 (n : ℕ) (s : Ω) :
      ((fun t => T (0, 1) t)^[n]) s = T (0, (n : ℤ)) s := by
    induction n with
    | zero => exact (hzero s).symm
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        have hpair : ((0 : ℤ), (1 : ℤ)) + ((0 : ℤ), (n : ℤ)) =
            ((0 : ℤ), ((n + 1 : ℕ) : ℤ)) := by
          ext <;> simp [Nat.cast_succ, add_comm]
        calc
          T (0, 1) (T (0, (n : ℤ)) s) =
              T (((0 : ℤ), 1) + (0, (n : ℤ))) s := (hadd (0, 1) (0, (n : ℤ)) s).symm
          _ = T (0, ((n + 1 : ℕ) : ℤ)) s := by
            exact congrArg (fun z : ℤ × ℤ => T z s) hpair

  have hHorizontal : ∀ᵐ s ∂μ, ∀ n : ℕ,
      g (T ((n : ℤ), 0) s) = g s := by
    have h := LPPDifferentiability.ae_all_iterate_eq_of_ae_invariant
      (hT (1, 0)) hInvariant0
    filter_upwards [h] with s hs
    intro n
    rw [← hIterate0 n s]
    exact hs n

  have hVertical : ∀ᵐ s ∂μ, ∀ n : ℕ,
      g (T (0, (n : ℤ)) s) = g s := by
    have h := LPPDifferentiability.ae_all_iterate_eq_of_ae_invariant
      (hT (0, 1)) hInvariant1
    filter_upwards [h] with s hs
    intro n
    rw [← hIterate1 n s]
    exact hs n

  -- Pull the horizontal event through every vertical shift before intersecting.
  have hHorizontalAtVertical : ∀ᵐ s ∂μ, ∀ y : ℕ, ∀ x : ℕ,
      g (T ((x : ℤ), 0) (T (0, (y : ℤ)) s)) = g (T (0, (y : ℤ)) s) := by
    apply ae_all_iff.mpr
    intro y
    exact (hT (0, (y : ℤ))).quasiMeasurePreserving.ae hHorizontal

  have hAllNonnegative : ∀ᵐ s ∂μ, ∀ x y : ℕ,
      g (T ((x : ℤ), (y : ℤ)) s) = g s := by
    filter_upwards [hVertical, hHorizontalAtVertical] with s hv hh
    intro x y
    have hAction : T ((x : ℤ), (y : ℤ)) s =
        T ((x : ℤ), 0) (T (0, (y : ℤ)) s) := by
      simpa using (hadd ((x : ℤ), 0) (0, (y : ℤ)) s)
    calc
      g (T ((x : ℤ), (y : ℤ)) s) =
          g (T ((x : ℤ), 0) (T (0, (y : ℤ)) s)) := by rw [hAction]
      _ = g (T (0, (y : ℤ)) s) := hh y x
      _ = g s := hv y

  -- On the common event, the sum is exactly the rectangle cardinality times g.
  have hSum (s : Ω) (hs : ∀ x y : ℕ,
      g (T ((x : ℤ), (y : ℤ)) s) = g s) (n : ℕ) :
      (∑ z ∈ R n, g (T z s)) = (R n).card • g s := by
    classical
    calc
      (∑ z ∈ R n, g (T z s)) = ∑ z ∈ R n, g s := by
        apply Finset.sum_congr rfl
        intro z hz
        rcases Finset.mem_product.mp hz with ⟨hz0, hz1⟩
        rcases Finset.mem_Ico.mp hz0 with ⟨hzx, _⟩
        rcases Finset.mem_Ico.mp hz1 with ⟨hzy, _⟩
        have hx : ((z.1.toNat : ℕ) : ℤ) = z.1 := Int.toNat_of_nonneg hzx
        have hy : ((z.2.toNat : ℕ) : ℤ) = z.2 := Int.toNat_of_nonneg hzy
        have hpair : (((z.1.toNat : ℕ) : ℤ), ((z.2.toNat : ℕ) : ℤ)) = z := by
          ext <;> assumption
        have h := hs z.1.toNat z.2.toNat
        rw [hpair] at h
        exact h
      _ = (R n).card • g s := by simp

  -- The product of the two floor side lengths is the rectangle cardinality.
  have hCard (n : ℕ) : (R n).card = A n * B n := by
    exact (integer_rectangle_difference_regularities (A n) (B n)).1

  -- Each floor side divided by n converges to its fixed positive side factor.
  have hFloor0 : Tendsto (fun n : ℕ => (A n : ℝ) / (n : ℝ)) atTop (𝓝 (b 0)) := by
    simpa only [A, Function.comp_def, mul_comm] using
      ((tendsto_nat_floor_mul_div_atTop (a := b 0) (hb 0).le).comp
        tendsto_natCast_atTop_atTop)
  have hFloor1 : Tendsto (fun n : ℕ => (B n : ℝ) / (n : ℝ)) atTop (𝓝 (b 1)) := by
    simpa only [B, Function.comp_def, mul_comm] using
      ((tendsto_nat_floor_mul_div_atTop (a := b 1) (hb 1).le).comp
        tendsto_natCast_atTop_atTop)

  have hAreaProduct : Tendsto
      (fun n : ℕ => ((A n : ℝ) / (n : ℝ)) * ((B n : ℝ) / (n : ℝ)))
      atTop (𝓝 (b 0 * b 1)) := hFloor0.mul hFloor1

  have hAreaRatio : Tendsto
      (fun n : ℕ => ((A n * B n : ℕ) : ℝ) / (n : ℝ)^2)
      atTop (𝓝 (b 0 * b 1)) := by
    apply hAreaProduct.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := by
      exact ne_of_gt (Nat.cast_pos.mpr (by omega))
    push_cast
    field_simp [hnR]

  -- Multiplying the scalar area limit by g(s) gives the desired limit.
  filter_upwards [hAllNonnegative] with s hs
  have hScalar : Tendsto
      (fun n : ℕ => (((A n * B n : ℕ) : ℝ) / (n : ℝ)^2) * g s)
      atTop (𝓝 (b 0 * b 1 * g s)) :=
    hAreaRatio.mul (tendsto_const_nhds : Tendsto (fun _ : ℕ => g s) atTop (𝓝 (g s)))
  apply hScalar.congr'
  filter_upwards [Filter.Eventually.of_forall (fun n => hSum s (hs · ·) n)] with n hsum
  rw [hsum, hCard n]
  push_cast
  ring

end ProbabilityBasics
