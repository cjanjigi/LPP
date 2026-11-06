/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Real

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Exponential tails on the planar nonnegative lattice

An exponential event bound indexed by the nonzero points of `ℕ × ℕ` is summable
and implies the first Borel–Cantelli conclusion. The event bound is a generic
conditional input; this module does not prove a passage-time concentration
estimate or an almost-sure statement about the LPP model.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace LPPDifferentiability

/-- Exponential weights on the planar nonnegative lattice are summable for a
positive rate. The proof groups the points into antidiagonal shells of size
`n + 1`. -/
theorem summable_lattice_exp_neg_of_pos {c : ℝ} (hc : 0 < c) :
    Summable (fun z : ℕ × ℕ =>
      Real.exp (-c * ((z.1 + z.2 : ℕ) : ℝ))) := by
  classical
  let shell : ℕ → Set (ℕ × ℕ) := fun n => (Finset.antidiagonal n : Set (ℕ × ℕ))
  let decay : (ℕ × ℕ) → ℝ := fun z =>
    Real.exp (-c * ((z.1 + z.2 : ℕ) : ℝ))
  have hpartition : ∀ z : ℕ × ℕ, ∃! n : ℕ, z ∈ shell n := by
    intro z
    refine ⟨z.1 + z.2, ?_, ?_⟩
    · change z ∈ Finset.antidiagonal (z.1 + z.2)
      exact Finset.mem_antidiagonal.mpr rfl
    · intro n hn
      change z ∈ Finset.antidiagonal n at hn
      exact (Finset.mem_antidiagonal.mp hn).symm
  have hseries : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) * Real.exp (-c * (n : ℝ))) := by
    have hgeom : Summable (fun n : ℕ => Real.exp (-c * (n : ℝ))) := by
      simpa only [mul_comm] using
        (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hc))
    have hlinear : Summable (fun n : ℕ =>
        (n : ℝ) * Real.exp (-c * (n : ℝ))) := by
      simpa only [pow_one] using Real.summable_pow_mul_exp_neg_nat_mul 1 hc
    have heq : (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) * Real.exp (-c * (n : ℝ))) =
        fun n : ℕ => (n : ℝ) * Real.exp (-c * (n : ℝ)) +
          Real.exp (-c * (n : ℝ)) := by
      funext n
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    rw [heq]
    exact hlinear.add hgeom
  have hshell (n : ℕ) : ∑' z : shell n, decay z.1 =
      ((n + 1 : ℕ) : ℝ) * Real.exp (-c * (n : ℝ)) := by
    let e : shell n ≃ Fin (n + 1) := Finset.Nat.antidiagonalEquivFin n
    calc
      ∑' z : shell n, decay z.1 =
          ∑' z : shell n, Real.exp (-c * (n : ℝ)) := by
        apply tsum_congr
        intro z
        have hz : z.1.1 + z.1.2 = n := Finset.mem_antidiagonal.mp z.2
        simp only [decay, hz]
      _ = ∑' i : Fin (n + 1), Real.exp (-c * (n : ℝ)) := by
        simpa only [Function.comp_apply] using
          e.tsum_eq (fun _ : Fin (n + 1) => Real.exp (-c * (n : ℝ)))
      _ = ((n + 1 : ℕ) : ℝ) * Real.exp (-c * (n : ℝ)) := by
        rw [tsum_fintype]
        simp [nsmul_eq_mul]
  have hinner : ∀ n : ℕ, Summable (fun z : shell n => decay z.1) := by
    intro n
    let e : shell n ≃ Fin (n + 1) := Finset.Nat.antidiagonalEquivFin n
    let f : Fin (n + 1) → ℝ := fun i => decay (e.symm i).1
    have hf : Summable f := (hasSum_fintype _).summable
    have h : Summable (fun z : shell n => decay (e.symm (e z)).1) :=
      e.summable_iff.mpr hf
    simpa only [Equiv.symm_apply_apply] using h
  have houter : Summable (fun n : ℕ => ∑' z : shell n, decay z.1) := by
    have heq : (fun n : ℕ => ∑' z : shell n, decay z.1) =
        fun n : ℕ => ((n + 1 : ℕ) : ℝ) * Real.exp (-c * (n : ℝ)) := by
      funext n
      exact hshell n
    rw [heq]
    exact hseries
  have hparts := summable_partition (f := decay)
    (fun z => Real.exp_nonneg _) (s := shell) hpartition
  exact hparts.mpr ⟨hinner, houter⟩

/-- A generic exponential probability bound away from the origin gives a finite
sum of event measures. The origin is left unrestricted and handled as one
finite exception. -/
theorem tsum_measure_ne_top_of_lattice_exp_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ × ℕ → Set Ω) {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (hTail : ∀ z : ℕ × ℕ, z ≠ (0, 0) →
      μ.real (A z) ≤ K * Real.exp (-c * ((z.1 + z.2 : ℕ) : ℝ))) :
    (∑' z : ℕ × ℕ, μ (A z)) ≠ ∞ := by
  classical
  let B : ℕ × ℕ → Set Ω := fun z => if z = (0, 0) then ∅ else A z
  have hbound (z : ℕ × ℕ) : μ.real (B z) ≤
      K * Real.exp (-c * ((z.1 + z.2 : ℕ) : ℝ)) := by
    by_cases hz : z = (0, 0)
    · simp [B, hz]
      exact hK
    · simpa [B, hz] using hTail z hz
  have hreal : Summable (fun z : ℕ × ℕ => μ.real (B z)) :=
    Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) hbound
      ((summable_lattice_exp_neg_of_pos hc).mul_left K)
  have htopB : (∑' z : ℕ × ℕ, μ (B z)) ≠ ∞ := by
    have hfinite (z : ℕ × ℕ) : μ (B z) ≠ ∞ := by
      apply ne_of_lt
      exact (prob_le_one (μ := μ) (s := B z)).trans_lt ENNReal.one_lt_top
    calc
      (∑' z : ℕ × ℕ, μ (B z)) =
          ∑' z : ℕ × ℕ, ENNReal.ofReal (μ.real (B z)) := by
        apply tsum_congr
        intro z
        exact (ofReal_measureReal (hfinite z)).symm
      _ = ENNReal.ofReal (∑' z : ℕ × ℕ, μ.real (B z)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hreal).symm
      _ ≠ ∞ := ENNReal.ofReal_ne_top
  have hsplit : (∑' z : ℕ × ℕ, μ (A z)) =
      μ (A (0, 0)) + ∑' z : ℕ × ℕ, μ (B z) := by
    rw [ENNReal.tsum_eq_add_tsum_ite (0, 0)]
    congr 1
    apply tsum_congr
    intro z
    by_cases hz : z = (0, 0) <;> simp [B, hz]
  rw [hsplit]
  apply ne_of_lt
  apply ENNReal.add_lt_top.mpr
  refine ⟨?_, lt_top_iff_ne_top.mpr htopB⟩
  exact (prob_le_one (μ := μ) (s := A (0, 0))).trans_lt ENNReal.one_lt_top

/-- Almost surely, only finitely many nonzero lattice points belong to their
events under a generic exponential tail bound. The origin is included in the
finite exceptional set. -/
theorem ae_finite_lattice_bad_set_of_exp_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ × ℕ → Set Ω) {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (hTail : ∀ z : ℕ × ℕ, z ≠ (0, 0) →
      μ.real (A z) ≤ K * Real.exp (-c * ((z.1 + z.2 : ℕ) : ℝ))) :
    ∀ᵐ ω ∂μ, {z : ℕ × ℕ | ω ∈ A z}.Finite := by
  exact MeasureTheory.ae_finite_setOfPred_mem
    (tsum_measure_ne_top_of_lattice_exp_tail μ A hK hc hTail)

end LPPDifferentiability
