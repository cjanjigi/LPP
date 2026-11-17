/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.Additive
public import Busemann.Frozen.Definitions.Recovery
public import LPP_Foundations.Model.LastPassage.Basic
public import LPP_Foundations.Model.LocalDefectPath
import LPP_Foundations.Model.RecoveryAntidiagonal

/-! Calibrated finite paths for an additive potential with pointwise recovery. -/
@[expose] public section
open LPPDifferentiability LPP.Busemann
open scoped BigOperators

namespace LPP.Busemann

/-- A path calibrated at each collected vertex has its potential value and is
maximizing; see GRS 1510.00860v2, Lemma 4.1(a). -/
theorem calibrated_path_weight_eq_and_maximizing
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (x : Lattice) (d : ℕ × ℕ)
    (p : LPPDifferentiability.Path x d)
    (hcal : ∀ k : Fin (d.1 + d.2),
      C (p.vertex k.castSucc) (p.vertex k.succ) =
        ω (p.vertex k.castSucc)) :
    pathWeight ω p = C x (x + ((d.1 : ℤ), (d.2 : ℤ))) ∧
      pathWeight ω p = lastPassage ω x d := by
  classical
  change ∀ a b c : Lattice, C a b + C b c = C a c at hC
  change ∀ z : Lattice,
    min (C z (z + ((1 : ℤ), (0 : ℤ))))
      (C z (z + ((0 : ℤ), (1 : ℤ)))) = ω z at hrec
  let n : ℕ := d.1 + d.2
  let v : Fin (n + 1) → Lattice := fun i => p.vertex i
  have hstart : v 0 = x := by
    dsimp [v]
    exact p.start
  have hfinish : v (Fin.last n) = x + ((d.1 : ℤ), (d.2 : ℤ)) := by
    dsimp [v, n]
    exact p.finish
  have hcalSum :
      (∑ i : Fin n, C (v i.castSucc) (v i.succ)) = pathWeight ω p := by
    calc
      _ = ∑ i : Fin n, ω (v i.castSucc) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hcal i
      _ = pathWeight ω p := rfl
  have hPotential : pathWeight ω p = C x (x + ((d.1 : ℤ), (d.2 : ℤ))) := by
    calc
      pathWeight ω p = ∑ i : Fin n, C (v i.castSucc) (v i.succ) := hcalSum.symm
      _ = C (v 0) (v (Fin.last n)) :=
        LPP.finite_edge_potential_telescope n C hC v
      _ = C x (x + ((d.1 : ℤ), (d.2 : ℤ))) := by rw [hstart, hfinish]
  have hAntidiagonal :=
    LPP.lastPassage_antidiagonal_comparison_and_attainment ω C hC hrec
  have hLastPassageLePotential :
      lastPassage ω x d ≤ C x (x + ((d.1 : ℤ), (d.2 : ℤ))) := by
    exact (hAntidiagonal x n).1 d rfl
  refine ⟨hPotential, ?_⟩
  apply le_antisymm
  · exact LPPDifferentiability.pathWeight_le_lastPassage ω p
  · rw [hPotential]
    exact hLastPassageLePotential

end LPP.Busemann
