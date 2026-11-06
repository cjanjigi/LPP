/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.PathSets
import Mathlib.Data.Int.Interval

/-! Actual collected sites meet each nonterminal level exactly once. -/

@[expose] public section

namespace LPPDifferentiability

/-- Collected local time is exactly the absolute level for paths from zero. -/
theorem Path.collected_level {d : ℕ × ℕ} (p : Path 0 d)
    (i : Fin (d.1 + d.2)) :
    (p.vertex i.castSucc).1 + (p.vertex i.castSucc).2 = (i.val : ℤ) := by
  simpa only [Prod.fst_zero, Prod.snd_zero, zero_add, Fin.val_castSucc] using
    p.level i.castSucc

/-- A collected site on a prescribed level is precisely the site at that local time. -/
theorem Path.collected_eq_iff_level {d : ℕ × ℕ} (p : Path 0 d)
    (i : Fin (d.1 + d.2)) {z : Lattice} (hz : z ∈ p.collectedSites) :
    z.1 + z.2 = (i.val : ℤ) ↔ z = p.vertex i.castSucc := by
  obtain ⟨j, rfl⟩ := (p.mem_collectedSites_iff z).mp hz
  rw [p.collected_level j]
  constructor
  · intro h
    have hji : j = i := Fin.ext (by omega)
    rw [hji]
  · intro h
    have hji := p.collectedSites_injective h
    rw [hji]

/-- Every declared collected level contains exactly one actual collected site. -/
theorem Path.existsUnique_collected_level {d : ℕ × ℕ} (p : Path 0 d)
    (i : Fin (d.1 + d.2)) :
    ∃! z : Lattice, z ∈ p.collectedSites ∧ z.1 + z.2 = (i.val : ℤ) := by
  refine ⟨p.vertex i.castSucc, ⟨p.vertex_mem_collectedSites i, p.collected_level i⟩, ?_⟩
  intro z hz
  exact (p.collected_eq_iff_level i hz.1).mp hz.2

/-- Collected vertices lie in the endpoint rectangle strictly below its terminal level. -/
theorem Path.collected_mem_box {d : ℕ × ℕ} (p : Path 0 d)
    {z : Lattice} (hz : z ∈ p.collectedSites) :
    z ∈ Set.Icc (0 : Lattice) ((d.1 : ℤ), (d.2 : ℤ)) ∧
      z.1 + z.2 < ((d.1 + d.2 : ℕ) : ℤ) := by
  obtain ⟨i, rfl⟩ := (p.mem_collectedSites_iff z).mp hz
  constructor
  · simpa only [zero_add] using p.vertex_mem_Icc i.castSucc
  · rw [p.collected_level i]
    exact_mod_cast i.isLt

/-- The literal collected endpoint box is finite, with no values outside it required. -/
theorem collected_box_finite (d : ℕ × ℕ) :
    {z : Lattice | z ∈ Set.Icc (0 : Lattice) ((d.1 : ℤ), (d.2 : ℤ)) ∧
      z.1 + z.2 < ((d.1 + d.2 : ℕ) : ℤ)}.Finite := by
  exact (Set.finite_Icc (0 : Lattice) ((d.1 : ℤ), (d.2 : ℤ))).subset
    (fun _ hz => hz.1)

/-- Every site in the literal box belongs to exactly one of the declared finite levels. -/
theorem collected_box_existsUnique_level {d : ℕ × ℕ} {z : Lattice}
    (hz : z ∈ Set.Icc (0 : Lattice) ((d.1 : ℤ), (d.2 : ℤ)))
    (hl : z.1 + z.2 < ((d.1 + d.2 : ℕ) : ℤ)) :
    ∃! k : Fin (d.1 + d.2), z.1 + z.2 = (k.val : ℤ) := by
  have hfst : 0 ≤ z.1 := hz.1.1
  have hsnd : 0 ≤ z.2 := hz.1.2
  refine ⟨⟨(z.1 + z.2).toNat, by omega⟩, ?_, ?_⟩
  · change z.1 + z.2 = ((z.1 + z.2).toNat : ℤ)
    omega
  · intro k hk
    apply Fin.ext
    dsimp only
    omega

end LPPDifferentiability
