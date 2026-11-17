/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LatticeEdgeIntegration
import Mathlib.Tactic

/-! Additivity and translation of the literal signed lattice edge sum. -/

public section

open scoped BigOperators

namespace LPPDifferentiability

/-- The signed edge formula is additive in its endpoints and translates with
the edge field, as in JR1810.03580v3, proof of Theorem 4.8 after (4.19). -/
theorem lattice_edge_extension_sum_additive_translation
    (E : Lattice → Fin 2 → ℝ)
    (hcurl : ∀ x, E x 0 + E (x + (1, 0)) 1 = E x 1 + E (x + (0, 1)) 0) :
    let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
      if a ≤ b then ∑ k ∈ Finset.Ico a b, f k else -(∑ k ∈ Finset.Ico b a, f k)
    let R : (Lattice → Fin 2 → ℝ) → Lattice → Lattice → ℝ := fun F x y =>
      S (fun k => F (k, x.2) 0) x.1 y.1 + S (fun k => F (y.1, k) 1) x.2 y.2
    (∀ x y z, R E x y + R E y z = R E x z) ∧
      (∀ z x y, R (fun u i => E (z + u) i) x y = R E (z + x) (z + y)) := by
  classical
  let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
    if a ≤ b then ∑ k ∈ Finset.Ico a b, f k else -(∑ k ∈ Finset.Ico b a, f k)
  let R : (Lattice → Fin 2 → ℝ) → Lattice → Lattice → ℝ := fun F x y =>
    S (fun k => F (k, x.2) 0) x.1 y.1 + S (fun k => F (y.1, k) 1) x.2 y.2
  change (∀ x y z, R E x y + R E y z = R E x z) ∧
    (∀ z x y, R (fun u i => E (z + u) i) x y = R E (z + x) (z + y))

  -- The integration theorem supplies the additive extension and formula.
  obtain ⟨B, hBadd, hBedge, hBR, _⟩ :=
    exists_unique_lattice_edge_extension E hcurl
  have hR_formula (x y : Lattice) : R E x y = B x y := by
    simpa only [R, S] using (hBR x y).symm
  constructor
  · intro x y z
    rw [hR_formula x y, hR_formula y z, hR_formula x z]
    exact hBadd x y z
  · intro z x y
    let Eshift : Lattice → Fin 2 → ℝ := fun u i => E (z + u) i
    have hcurl_shift :
        ∀ u, Eshift u 0 + Eshift (u + (1, 0)) 1 =
          Eshift u 1 + Eshift (u + (0, 1)) 0 := by
      intro u
      simpa only [Eshift, add_assoc] using hcurl (z + u)
    -- Apply the same integration and uniqueness result to the shifted field.
    obtain ⟨Bshift, _, _, hBshiftR, hBshiftUnique⟩ :=
      exists_unique_lattice_edge_extension Eshift hcurl_shift
    have hRshift_formula (a b : Lattice) : R Eshift a b = Bshift a b := by
      simpa only [R, S] using (hBshiftR a b).symm
    let C : Lattice → Lattice → ℝ := fun a b => B (z + a) (z + b)
    have hCadd : ∀ a b c, C a b + C b c = C a c := by
      intro a b c
      dsimp only [C]
      exact hBadd (z + a) (z + b) (z + c)
    have hCedge : ∀ a,
        C a (a + (1, 0)) = Eshift a 0 ∧ C a (a + (0, 1)) = Eshift a 1 := by
      intro a
      constructor
      · dsimp only [C, Eshift]
        simpa only [add_assoc] using (hBedge (z + a)).1
      · dsimp only [C, Eshift]
        simpa only [add_assoc] using (hBedge (z + a)).2
    have hCeq : C = Bshift := hBshiftUnique C hCadd hCedge
    calc
      R Eshift x y = Bshift x y := hRshift_formula x y
      _ = C x y := by rw [hCeq]
      _ = B (z + x) (z + y) := rfl
      _ = R E (z + x) (z + y) := (hR_formula (z + x) (z + y)).symm

end LPPDifferentiability
