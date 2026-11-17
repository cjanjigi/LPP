/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants

import Mathlib.Tactic.Ring

/-! The invariant sigma algebra of a generic signed column action is the one-step invariant sigma algebra. -/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- Invariance under all signed shifts in one coordinate is exactly invariance
under its unit shift for an action satisfying the zero and addition laws. -/
theorem unit_column_invariants_of_action
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (T : Lattice → Ω → Ω) (hzero : ∀ s : Ω, T 0 s = s)
    (hadd : ∀ (z w : Lattice) (s : Ω), T (z + w) s = T z (T w s))
    (i : Fin 2) :
    let mΩ0 : MeasurableSpace Ω := inferInstance
    let e : Lattice := finiteEdgeStep i
    let Tcol : Lattice → Ω → Ω := fun z s => T (z.1 • e) s
    let Icol : MeasurableSpace Ω := ⨅ z : Lattice,
      @MeasurableSpace.invariants Ω mΩ0 (Tcol z)
    let J : MeasurableSpace Ω := @MeasurableSpace.invariants Ω mΩ0 (T e)
    Icol = J := by
  classical
  let mΩ0 : MeasurableSpace Ω := inferInstance
  let e : Lattice := finiteEdgeStep i
  let Tcol : Lattice → Ω → Ω := fun z s => T (z.1 • e) s
  let Icol : MeasurableSpace Ω := ⨅ z : Lattice,
    @MeasurableSpace.invariants Ω mΩ0 (Tcol z)
  let J : MeasurableSpace Ω := @MeasurableSpace.invariants Ω mΩ0 (T e)
  let : MeasurableSpace Ω := mΩ0
  change Icol = J

  have hIter (a : Lattice) (n : ℕ) (s : Ω) :
      (T a)^[n] s = T ((n : ℤ) • a) s := by
    induction n with
    | zero =>
        simp only [Function.iterate_zero_apply, Nat.cast_zero]
        have hscalar : (0 : ℤ) • a = (0 : Lattice) := by ext <;> simp
        rw [hscalar, hzero]
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        calc
          T a (T ((n : ℤ) • a) s) = T (a + (n : ℤ) • a) s :=
            (hadd a ((n : ℤ) • a) s).symm
          _ = T (((n + 1 : ℕ) : ℤ) • a) s := by
            congr 1
            ext <;> simp [Nat.cast_succ] <;> ring

  let f : Ω → Ω := T e
  let fInv : Ω → Ω := T (-e)
  have hRightInv : f ∘ fInv = id := by
    funext s
    change T e (T (-e) s) = s
    calc
      T e (T (-e) s) = T (e + -e) s := (hadd e (-e) s).symm
      _ = T 0 s := by
        have he : e + -e = (0 : Lattice) := by ext <;> simp
        rw [he]
      _ = s := hzero s
  have hInvNeg : J ≤ @MeasurableSpace.invariants Ω mΩ0 fInv := by
    intro A hA
    rcases MeasurableSpace.measurableSet_invariants.mp hA with ⟨hAm, hInv⟩
    apply MeasurableSpace.measurableSet_invariants.mpr
    refine ⟨hAm, ?_⟩
    calc
      fInv ⁻¹' A = fInv ⁻¹' (f ⁻¹' A) := by rw [hInv]
      _ = (f ∘ fInv) ⁻¹' A := by ext s; rfl
      _ = A := by rw [hRightInv]; simp

  apply le_antisymm
  · dsimp only [Icol, J]
    have hunit : Tcol (1, 0) = T e := by
      have hscalar : (1 : ℤ) • e = e := by ext <;> simp
      funext s
      change T ((1 : ℤ) • e) s = T e s
      rw [hscalar]
    rw [← hunit]
    exact iInf_le (fun z : Lattice =>
      @MeasurableSpace.invariants Ω mΩ0 (Tcol z)) (1, 0)
  · change J ≤ ⨅ z : Lattice,
      @MeasurableSpace.invariants Ω mΩ0 (Tcol z)
    rw [le_iInf_iff]
    intro z
    rcases z with ⟨j, _⟩
    change J ≤ @MeasurableSpace.invariants Ω mΩ0 (T (j • e))
    cases j with
    | ofNat n =>
        have hPow : (T e)^[n] = T ((Int.ofNat n : ℤ) • e) := by
          funext s
          exact hIter e n s
        rw [← hPow]
        change @MeasurableSpace.invariants Ω mΩ0 (T e) ≤
          @MeasurableSpace.invariants Ω mΩ0 ((T e)^[n])
        exact MeasurableSpace.le_invariants_iterate (T e) n
    | negSucc n =>
        have hPow : (T (-e))^[n + 1] = T ((Int.negSucc n : ℤ) • e) := by
          funext s
          calc
            (T (-e))^[n + 1] s = T (((n + 1 : ℕ) : ℤ) • (-e)) s :=
              hIter (-e) (n + 1) s
            _ = T ((Int.negSucc n : ℤ) • e) s := by
              congr 1
              ext <;> simp [Int.negSucc_eq] <;> ring
        rw [← hPow]
        change @MeasurableSpace.invariants Ω mΩ0 (T e) ≤
          @MeasurableSpace.invariants Ω mΩ0 ((T (-e))^[n + 1])
        exact hInvNeg.trans
          (MeasurableSpace.le_invariants_iterate (T (-e)) (n + 1))

end LPP.Busemann
