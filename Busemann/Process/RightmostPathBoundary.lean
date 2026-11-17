/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.Additive
public import Busemann.Frozen.Definitions.OutsideLowerOrthants
public import Busemann.Frozen.Definitions.FiniteEdgeStep
import LPP_Foundations.Model.LocalDefectPath
import Mathlib.Tactic

/-! Equality of additive potentials along the two shielding boundaries. -/

@[expose] public section

open LPPDifferentiability LPP.Busemann

namespace LPP.Busemann

/-- The two recovering potentials have the same increment along a north
boundary segment when every modified site lies strictly below that boundary. -/
theorem rightmost_north_boundary_potential_eq
    (C C' : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hC' : is_additive C')
    (V : Finset Lattice) (M2 a b : ℤ)
    (hBox : ∀ z ∈ V, z.2 < M2)
    (hEdges : ∀ y : Lattice, y ∈ outsideLowerOrthants V →
      ∀ i : Fin 2,
        C' y (y + finiteEdgeStep i) = C y (y + finiteEdgeStep i))
    (hab : a ≤ b) :
    C' (a, M2) (b, M2) = C (a, M2) (b, M2) := by
  change ∀ x y z, C x y + C y z = C x z at hC
  change ∀ x y z, C' x y + C' y z = C' x z at hC'
  let n : ℕ := Int.toNat (b - a)
  have hn : (n : ℤ) = b - a := by
    dsimp [n]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hab)
  let v : Fin (n + 1) → Lattice := fun i => (a + (i.val : ℤ), M2)
  have hstart : v 0 = (a, M2) := by
    apply Prod.ext
    · simp [v]
    · rfl
  have hfinish : v (Fin.last n) = (b, M2) := by
    apply Prod.ext
    · simp only [v, Fin.val_last]
      omega
    · rfl
  have hstep (i : Fin n) :
      v i.succ = v i.castSucc + (1, 0) := by
    apply Prod.ext
    · simp only [v, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one,
        Prod.fst_add]
      omega
    · simp [v]
  have hout (i : Fin n) : v i.castSucc ∈ outsideLowerOrthants V := by
    change ∀ z ∈ V, ¬ v i.castSucc ≤ z
    intro z hz hle
    exact (not_le_of_gt (hBox z hz)) (hle.2)
  have hedge (i : Fin n) :
      C' (v i.castSucc) (v i.succ) = C (v i.castSucc) (v i.succ) := by
    have he := hEdges (v i.castSucc) (hout i) (0 : Fin 2)
    have he' : C' (v i.castSucc) (v i.castSucc + (1, 0)) =
        C (v i.castSucc) (v i.castSucc + (1, 0)) := by
      simpa [finiteEdgeStep] using he
    rw [hstep i]
    exact he'
  calc
    C' (a, M2) (b, M2) =
        ∑ i : Fin n, C' (v i.castSucc) (v i.succ) := by
          rw [← hstart, ← hfinish]
          exact (LPP.finite_edge_potential_telescope n C' hC' v).symm
    _ = ∑ i : Fin n, C (v i.castSucc) (v i.succ) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hedge i
    _ = C (a, M2) (b, M2) := by
          rw [LPP.finite_edge_potential_telescope n C hC v, hstart, hfinish]

/-- The two recovering potentials have the same increment along an east
boundary segment when every modified site lies strictly left of that boundary. -/
theorem rightmost_east_boundary_potential_eq
    (C C' : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hC' : is_additive C')
    (V : Finset Lattice) (M1 a b : ℤ)
    (hBox : ∀ z ∈ V, z.1 < M1)
    (hEdges : ∀ y : Lattice, y ∈ outsideLowerOrthants V →
      ∀ i : Fin 2,
        C' y (y + finiteEdgeStep i) = C y (y + finiteEdgeStep i))
    (hab : a ≤ b) :
    C' (M1, a) (M1, b) = C (M1, a) (M1, b) := by
  change ∀ x y z, C x y + C y z = C x z at hC
  change ∀ x y z, C' x y + C' y z = C' x z at hC'
  let n : ℕ := Int.toNat (b - a)
  have hn : (n : ℤ) = b - a := by
    dsimp [n]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hab)
  let v : Fin (n + 1) → Lattice := fun i => (M1, a + (i.val : ℤ))
  have hstart : v 0 = (M1, a) := by
    apply Prod.ext
    · rfl
    · simp [v]
  have hfinish : v (Fin.last n) = (M1, b) := by
    apply Prod.ext
    · rfl
    · simp only [v, Fin.val_last]
      omega
  have hstep (i : Fin n) :
      v i.succ = v i.castSucc + (0, 1) := by
    apply Prod.ext
    · simp [v]
    · simp only [v, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one,
        Prod.snd_add]
      omega
  have hout (i : Fin n) : v i.castSucc ∈ outsideLowerOrthants V := by
    change ∀ z ∈ V, ¬ v i.castSucc ≤ z
    intro z hz hle
    exact (not_le_of_gt (hBox z hz)) (hle.1)
  have hedge (i : Fin n) :
      C' (v i.castSucc) (v i.succ) = C (v i.castSucc) (v i.succ) := by
    have he := hEdges (v i.castSucc) (hout i) (1 : Fin 2)
    have he' : C' (v i.castSucc) (v i.castSucc + (0, 1)) =
        C (v i.castSucc) (v i.castSucc + (0, 1)) := by
      simpa [finiteEdgeStep] using he
    rw [hstep i]
    exact he'
  calc
    C' (M1, a) (M1, b) =
        ∑ i : Fin n, C' (v i.castSucc) (v i.succ) := by
          rw [← hstart, ← hfinish]
          exact (LPP.finite_edge_potential_telescope n C' hC' v).symm
    _ = ∑ i : Fin n, C (v i.castSucc) (v i.succ) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hedge i
    _ = C (M1, a) (M1, b) := by
          rw [LPP.finite_edge_potential_telescope n C hC v, hstart, hfinish]

end LPP.Busemann
