/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.NorthBoundaryExitFormula
public import LPP_Foundations.Model.LastPassage.Swap

/-! Transport the finite north-boundary exit formula across coordinate transposition. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- The last-passage value with only the east boundary changed is the maximum
over all vertical exit locations. This is the coordinate-swapped version of
the derived one-sided exit formula related to GRS 1510.00859v2, Lemma 6.4;
its two-boundary NE passage is defined in (6.8). -/
theorem east_boundary_passage_eq_exit_sup
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (x : Lattice) (d : ℕ × ℕ) :
    let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
    let E : Environment := fun z =>
      if z.1 = v.1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z
    lastPassage E x d =
      (Finset.univ : Finset (Fin (d.2 + 1))).sup' Finset.univ_nonempty
        (fun k => lastPassage ω x (d.1, d.2 - k.val) +
          C (v - (0, (k.val : ℤ))) v) := by
  let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
  let E : Environment := fun z =>
    if z.1 = v.1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z
  let ωS : Environment := fun z => ω z.swap
  let CS : Lattice → Lattice → ℝ := fun u w => C u.swap w.swap
  let xS : Lattice := x.swap
  let dS : ℕ × ℕ := d.swap
  let vS : Lattice := xS + ((dS.1 : ℤ), (dS.2 : ℤ))
  let N : Environment := fun z =>
    if z.2 = vS.2 ∧ z.1 < vS.1 then CS z (z + (1, 0)) else ωS z
  change lastPassage E x d =
    (Finset.univ : Finset (Fin (d.2 + 1))).sup' Finset.univ_nonempty
      (fun k => lastPassage ω x (d.1, d.2 - k.val) +
        C (v - (0, (k.val : ℤ))) v)
  -- Additivity and recovery retain the original hypotheses after swapping.
  have hCS : is_additive CS := by
    intro a b c
    exact hC a.swap b.swap c.swap
  have hrecS : recovers_environment ωS CS := by
    intro z
    have hz := hrec z.swap
    simpa [CS, ωS, Prod.swap, Prod.swap_add, min_comm] using hz
  -- The changed north field is the east field seen through the swap.
  have hvS : vS = v.swap := by
    simp [vS, v, xS, dS, Prod.swap_add]
  have hfield (z : Lattice) : N z = E z.swap := by
    simp [N, E, CS, ωS, hvS, Prod.swap]
  -- Invoke the north identity without repeating its first-exit proof.
  have hnorth := north_boundary_passage_eq_exit_sup ωS CS hCS hrecS xS dS
  change lastPassage N xS dS =
    (Finset.univ : Finset (Fin (d.2 + 1))).sup' Finset.univ_nonempty
      (fun k => lastPassage ωS xS (d.2 - k.val, d.1) +
        CS (vS - ((k.val : ℤ), 0)) vS) at hnorth
  have hleft : lastPassage N xS dS = lastPassage E x d := by
    rw [show N = (fun z => E z.swap) from funext hfield]
    simpa only [xS, dS, Prod.swap_swap] using
      (lastPassage_swap E xS dS).symm
  -- Each north objective is exactly the corresponding east objective.
  have hobjective (k : Fin (d.2 + 1)) :
      lastPassage ωS xS (d.2 - k.val, d.1) +
          CS (vS - ((k.val : ℤ), 0)) vS =
        lastPassage ω x (d.1, d.2 - k.val) +
          C (v - (0, (k.val : ℤ))) v := by
    have hpassage := lastPassage_swap ω xS (d.2 - k.val, d.1)
    have hpassageS :
        lastPassage ωS xS (d.2 - k.val, d.1) =
          lastPassage ω x (d.1, d.2 - k.val) := by
      simpa [ωS, xS, Prod.swap] using hpassage.symm
    rw [hpassageS]
    simp [CS, hvS, Prod.swap]
    have htail : (v.1, v.2 - (k.val : ℤ)) = v - (0, (k.val : ℤ)) := by
      ext <;> simp
    rw [htail]
  rw [← hleft]
  simpa only [hobjective] using hnorth

end LPP.Busemann
