/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Probability.PathArrowCylinder
public import LPP_Foundations.Model.Path.ArrowOrder
public import LPP_Foundations.Model.Paths.Fintype
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Endpoint expectations for a single sitewise uniform arrow field. -/

@[expose] public section

open MeasureTheory
open scoped BigOperators unitInterval

namespace LPPDifferentiability

/-- The actual finite arrow endpoint has the trace-cylinder expectation and
obeys the integrated same-arrow sandwich, as in JR1810.03580v3, Appendix A.1. -/
theorem uniform_arrow_endpoint_expectation (a : Lattice → unitInterval) :
    let Q : Measure (Lattice → unitInterval) :=
      Measure.infinitePi (fun _ : Lattice => (volume : Measure unitInterval))
    let A : (Lattice → unitInterval) → Lattice → Lattice := fun θ y =>
      if θ y < a y then y + (1, 0) else y + (0, 1)
    let E : ℕ → Lattice → (Lattice → unitInterval) → ℝ := fun N x θ =>
      (((A θ)^[N] x).1 : ℝ) - (x.1 : ℝ)
    let Gamma : (N : ℕ) → (x : Lattice) →
        (Σ k : Fin (N + 1), LPPDifferentiability.Path x (k.val, N - k.val)) →
        Set (Lattice → unitInterval) := fun N x q =>
      {θ | ∀ j : ℕ, ∀ hj : j < q.1.val + (N - q.1.val) + 1,
        q.2.vertex ⟨j, hj⟩ = (A θ)^[j] x}
    (∀ N x, Integrable (E N x) Q ∧
      (∫ θ, E N x θ ∂Q) =
        ∑ k : Fin (N + 1), ∑ p : LPPDifferentiability.Path x (k.val, N - k.val),
          (k.val : ℝ) * (Q (Gamma N x ⟨k, p⟩)).toReal) ∧
    (∀ N x, (∫ θ, E N (x + (0, 1)) θ ∂Q) ≤ ∫ θ, E (N + 1) x θ ∂Q) ∧
    (∀ N x, (∫ θ, E (N + 1) x θ ∂Q) ≤
      (∫ θ, E N (x + (1, 0)) θ ∂Q) + 1) := by
  classical
  let Q : Measure (Lattice → unitInterval) :=
    Measure.infinitePi (fun _ : Lattice => (volume : Measure unitInterval))
  let A : (Lattice → unitInterval) → Lattice → Lattice := fun θ y =>
    if θ y < a y then y + (1, 0) else y + (0, 1)
  let E : ℕ → Lattice → (Lattice → unitInterval) → ℝ := fun N x θ =>
    (((A θ)^[N] x).1 : ℝ) - (x.1 : ℝ)
  let Gamma : (N : ℕ) → (x : Lattice) →
      (Σ k : Fin (N + 1), LPPDifferentiability.Path x (k.val, N - k.val)) →
      Set (Lattice → unitInterval) := fun N x q =>
    {θ | ∀ j : ℕ, ∀ hj : j < q.1.val + (N - q.1.val) + 1,
      q.2.vertex ⟨j, hj⟩ = (A θ)^[j] x}
  let : IsProbabilityMeasure Q := by dsimp only [Q]; infer_instance
  have hArrow (θ : Lattice → unitInterval) (y : Lattice) :
      A θ y = y + (1, 0) ∨ A θ y = y + (0, 1) := by
    dsimp only [A]
    split_ifs <;> simp

  -- Actual trace cylinders are measurable by the fixed-path theorem.
  have hGamma (N : ℕ) (x : Lattice)
      (q : Σ k : Fin (N + 1), LPPDifferentiability.Path x (k.val, N - k.val)) :
      MeasurableSet (Gamma N x q) := by
    have hc := (uniform_arrow_path_cylinder a x (q.1.val, N - q.1.val) q.2).1
    have heq : Gamma N x q =
        {θ | ∀ j : Fin (q.1.val + (N - q.1.val) + 1),
          ((A θ)^[j.val]) x = q.2.vertex j} := by
      ext θ
      constructor
      · intro ht j
        exact (ht j.val j.isLt).symm
      · intro ht j hj
        exact (ht ⟨j, hj⟩).symm
    rw [heq]
    exact hc

  have hformula (N : ℕ) (x : Lattice) : Integrable (E N x) Q ∧
      (∫ θ, E N x θ ∂Q) =
        ∑ k : Fin (N + 1), ∑ p : LPPDifferentiability.Path x (k.val, N - k.val),
          (k.val : ℝ) * (Q (Gamma N x ⟨k, p⟩)).toReal := by
    let TraceIndex := Σ k : Fin (N + 1), LPPDifferentiability.Path x (k.val, N - k.val)
    let term : TraceIndex → (Lattice → unitInterval) → ℝ := fun q =>
      (Gamma N x q).indicator (fun _ => (q.1.val : ℝ))
    have hterm (q : TraceIndex) : Integrable (term q) Q :=
      (integrable_const (q.1.val : ℝ)).indicator (hGamma N x q)
    have hendpoint (θ : Lattice → unitInterval) (q : TraceIndex) (hq : θ ∈ Gamma N x q) :
        E N x θ = (q.1.val : ℝ) := by
      have hk := q.1.isLt
      have hlen : q.1.val + (N - q.1.val) = N := by omega
      have ht := hq N (by omega)
      have hi : (⟨N, by omega⟩ : Fin (q.1.val + (N - q.1.val) + 1)) =
          Fin.last (q.1.val + (N - q.1.val)) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      have hfinish : q.2.vertex ⟨N, by omega⟩ =
          x + ((q.1.val : ℤ), ((N - q.1.val : ℕ) : ℤ)) := by
        rw [hi]
        exact q.2.finish
      have hf := congrArg Prod.fst (ht.symm.trans hfinish)
      simp only [Prod.fst_add] at hf
      dsimp only [E]
      rw [hf]
      push_cast
      ring
    have hsum (θ : Lattice → unitInterval) : E N x θ = ∑ q : TraceIndex, term q θ := by
      obtain ⟨q, hq, hUnique⟩ := exists_unique_arrow_iterate_path_trace (A θ) (hArrow θ) x N
      have hqmem : θ ∈ Gamma N x q := hq
      have hsingle : (∑ r : TraceIndex, term r θ) = term q θ := by
        apply Finset.sum_eq_single q
        · intro r hr hrq
          have hn : θ ∉ Gamma N x r := by
            intro ht
            exact hrq (hUnique r ht)
          simp only [term, Set.indicator_of_notMem hn]
        · intro hqnot
          exact (hqnot (Finset.mem_univ q)).elim
      rw [hsingle]
      change E N x θ = (Gamma N x q).indicator (fun _ => (q.1.val : ℝ)) θ
      rw [Set.indicator_of_mem hqmem]
      exact hendpoint θ q hqmem
    have hint : Integrable (E N x) Q := by
      have hs : Integrable (fun θ => ∑ q : TraceIndex, term q θ) Q :=
        integrable_finsetSum _ (fun q _ => hterm q)
      exact hs.congr (Filter.Eventually.of_forall fun θ => (hsum θ).symm)
    refine ⟨hint, ?_⟩
    calc
      (∫ θ, E N x θ ∂Q) = ∫ θ, ∑ q : TraceIndex, term q θ ∂Q := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hsum
      _ = ∑ q : TraceIndex, ∫ θ, term q θ ∂Q := integral_finsetSum _ (fun q _ => hterm q)
      _ = ∑ q : TraceIndex, (q.1.val : ℝ) * (Q (Gamma N x q)).toReal := by
        apply Finset.sum_congr rfl
        intro q hq
        change (∫ θ, (Gamma N x q).indicator (fun _ => (q.1.val : ℝ)) θ ∂Q) = _
        rw [integral_indicator_const _ (hGamma N x q)]
        simp only [measureReal_def, smul_eq_mul, mul_comm]
      _ = _ := by rw [Fintype.sum_sigma]

  refine ⟨hformula, ?_, ?_⟩
  · intro N x
    apply integral_mono (hformula N (x + (0, 1))).1 (hformula (N + 1) x).1
    intro θ
    have hs := (iterate_arrow_endpoint_sandwich (A θ) (hArrow θ) x N).1
    have hr : (((A θ)^[N] (x + (0, 1))).1 : ℝ) ≤
        (((A θ)^[N + 1] x).1 : ℝ) := by exact_mod_cast hs
    dsimp only [E, Prod.fst_add]
    push_cast
    linarith
  · intro N x
    have hi : Integrable (fun θ => E N (x + (1, 0)) θ + 1) Q :=
      ((hformula N (x + (1, 0))).1).add (integrable_const 1)
    have hb : (∫ θ, E (N + 1) x θ ∂Q) ≤
        ∫ θ, E N (x + (1, 0)) θ + 1 ∂Q := by
      apply integral_mono (hformula (N + 1) x).1 hi
      intro θ
      have hs := (iterate_arrow_endpoint_sandwich (A θ) (hArrow θ) x N).2
      have hr : (((A θ)^[N + 1] x).1 : ℝ) ≤
          (((A θ)^[N] (x + (1, 0))).1 : ℝ) := by exact_mod_cast hs
      dsimp only [E, Prod.fst_add]
      push_cast
      linarith
    simpa only [integral_add (hformula N (x + (1, 0))).1 (integrable_const 1),
      integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hb

end LPPDifferentiability
