/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Geometry
public import LPP_Foundations.Model.Animals.Family
public import LPP_Foundations.Frozen.Model.PathWeight

/-! The collected sites of an up-right path exclude its terminal vertex.
Positive-length paths starting at zero give rooted lattice animals. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- The path sites at local times strictly before the terminal time. -/
noncomputable def Path.collectedSites {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    Finset Lattice :=
  Finset.univ.image (fun i : Fin (d.1 + d.2) => p.vertex i.castSucc)

/-- Membership is exactly occurrence at a nonterminal local time. -/
theorem Path.mem_collectedSites_iff {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (z : Lattice) :
    z ∈ p.collectedSites ↔ ∃ i : Fin (d.1 + d.2), p.vertex i.castSucc = z := by
  classical
  simp only [Path.collectedSites, Finset.mem_image, Finset.mem_univ, true_and]

/-- Every nonterminal local time supplies a collected site. -/
theorem Path.vertex_mem_collectedSites {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (i : Fin (d.1 + d.2)) : p.vertex i.castSucc ∈ p.collectedSites :=
  (p.mem_collectedSites_iff _).2 ⟨i, rfl⟩

/-- Distinct nonterminal local times supply distinct sites. -/
theorem Path.collectedSites_injective {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    Function.Injective (fun i : Fin (d.1 + d.2) => p.vertex i.castSucc) := by
  intro i j hij
  have h := p.vertex_injective hij
  exact Fin.castSucc_injective _ h

/-- The number of collected sites is exactly the coordinate-sum displacement. -/
theorem Path.collectedSites_card {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    p.collectedSites.card = d.1 + d.2 := by
  classical
  rw [Path.collectedSites, Finset.card_image_of_injective _ p.collectedSites_injective,
    Finset.card_univ, Fintype.card_fin]

/-- The terminal site is excluded, including for zero displacement. -/
theorem Path.finish_notMem_collectedSites {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    u + ((d.1 : ℤ), (d.2 : ℤ)) ∉ p.collectedSites := by
  intro h
  obtain ⟨i, hi⟩ := (p.mem_collectedSites_iff _).mp h
  rw [← p.finish] at hi
  have hval := congrArg Fin.val (p.vertex_injective hi)
  simp only [Fin.val_castSucc, Fin.val_last] at hval
  omega

/-- Signed path weight is exactly the sum over the collected sites. -/
theorem Path.pathWeight_eq_sum_collectedSites (ω : Environment)
    {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    pathWeight ω p = ∑ z ∈ p.collectedSites, ω z := by
  classical
  rw [Path.collectedSites, Finset.sum_image]
  · rfl
  · intro i _ j _ hij
    exact p.collectedSites_injective hij

/-- A path of zero displacement collects no site. -/
theorem Path.collectedSites_zero {u : Lattice} (p : Path u (0, 0)) :
    p.collectedSites = ∅ := by
  classical
  exact Finset.card_eq_zero.mp p.collectedSites_card

/-- Positive-length paths collect their initial site. -/
theorem Path.start_mem_collectedSites {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (hd : 0 < d.1 + d.2) : u ∈ p.collectedSites := by
  apply (p.mem_collectedSites_iff u).2
  exact ⟨⟨0, hd⟩, p.start⟩

private theorem path_step_adj {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (i : Fin (d.1 + d.2)) :
    nearestNeighborGraph.Adj (p.vertex i.castSucc) (p.vertex i.succ) := by
  rcases p.step i with h | h
  · rw [h]
    left
    simp only [Prod.fst_add, Prod.snd_add, add_zero, sub_add_cancel_left,
      abs_neg, abs_one, and_self]
  · rw [h]
    right
    simp only [Prod.fst_add, Prod.snd_add, add_zero, sub_add_cancel_left,
      abs_neg, abs_one, and_self]

private theorem path_collectedSites_reachable {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (hd : 0 < d.1 + d.2) :
    ∀ k (hk : k < d.1 + d.2),
      (nearestNeighborGraph.induce (↑p.collectedSites : Set Lattice)).Reachable
        ⟨u, p.start_mem_collectedSites hd⟩
        ⟨p.vertex (⟨k, hk⟩ : Fin (d.1 + d.2)).castSucc,
          p.vertex_mem_collectedSites ⟨k, hk⟩⟩ := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h : (⟨p.vertex (⟨0, hk⟩ : Fin (d.1 + d.2)).castSucc,
        p.vertex_mem_collectedSites ⟨0, hk⟩⟩ : p.collectedSites) =
        ⟨u, p.start_mem_collectedSites hd⟩ := Subtype.ext p.start
    rw [h]
  | succ k ih =>
    intro hk
    have hk' : k < d.1 + d.2 := by omega
    apply (ih hk').trans
    apply SimpleGraph.Adj.reachable
    change nearestNeighborGraph.Adj
      (p.vertex (⟨k, hk'⟩ : Fin (d.1 + d.2)).castSucc)
      (p.vertex (⟨k + 1, hk⟩ : Fin (d.1 + d.2)).castSucc)
    exact path_step_adj p ⟨k, hk'⟩

/-- Consecutive path steps connect all collected sites in their induced graph. -/
theorem Path.collectedSites_isConnected {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (hd : 0 < d.1 + d.2) : IsConnectedAnimal p.collectedSites := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨⟨u, p.start_mem_collectedSites hd⟩, ?_⟩
  rintro ⟨z, hz⟩
  obtain ⟨i, rfl⟩ := (p.mem_collectedSites_iff z).mp hz
  exact path_collectedSites_reachable p hd i.val i.isLt

/-- A positive-length path from zero is, as a set of sites, an animal of its size. -/
theorem Path.collectedSites_mem_animalFamily {d : ℕ × ℕ} (p : Path 0 d)
    (hd : 0 < d.1 + d.2) : p.collectedSites ∈ animalFamily (d.1 + d.2) :=
  (mem_animalFamily_iff _ _).2
    ⟨p.collectedSites_isConnected hd, p.start_mem_collectedSites hd,
      p.collectedSites_card⟩

end LPPDifferentiability
