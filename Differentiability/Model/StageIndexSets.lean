/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Finite images of lattice sequences with bounded coordinate increments. -/

public section

namespace LPPDifferentiability

/-- A finite lattice sequence has a connected radius-two image when it starts at zero
and each consecutive pair differs by at most two in each coordinate. -/
theorem stage_index_image_connected {N : ℕ} (c : Fin (N + 1) → Lattice)
    (hc : c 0 = 0)
    (hstep : ∀ i : Fin N,
      |(c i.succ).1 - (c i.castSucc).1| ≤ 2 ∧
      |(c i.succ).2 - (c i.castSucc).2| ≤ 2) :
    let A := Finset.univ.image c
    A.card ≤ N + 1 ∧
    (0 : Lattice) ∈ A ∧
    ((SimpleGraph.fromRel (fun x y : Lattice =>
      |x.1 - y.1| ≤ 2 ∧ |x.2 - y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected := by
  classical
  let A : Finset Lattice := Finset.univ.image c
  have hcard : A.card ≤ N + 1 := by
    calc
      A.card ≤ (Finset.univ : Finset (Fin (N + 1))).card := Finset.card_image_le
      _ = N + 1 := by simp
  have hzero : (0 : Lattice) ∈ A :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hc⟩
  let G : SimpleGraph Lattice := SimpleGraph.fromRel (fun x y : Lattice =>
    |x.1 - y.1| ≤ 2 ∧ |x.2 - y.2| ≤ 2)
  let H : SimpleGraph {x : Lattice // x ∈ A} := G.induce (↑A : Set Lattice)
  let node (i : Fin (N + 1)) : {x : Lattice // x ∈ A} :=
    ⟨c i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hstepReach (i : Fin N) : H.Reachable (node i.castSucc) (node i.succ) := by
    by_cases heq : c i.castSucc = c i.succ
    · have hnode : node i.castSucc = node i.succ := Subtype.ext heq
      rw [hnode]
    · apply SimpleGraph.Adj.reachable
      rw [SimpleGraph.induce_adj, SimpleGraph.fromRel_adj]
      exact ⟨heq, Or.inr (hstep i)⟩
  have hroot (i : Fin (N + 1)) : H.Reachable (node 0) (node i) := by
    induction i using Fin.induction with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ i hi => exact hi.trans (hstepReach i)
  have hconnected : H.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨node 0, fun w => ?_⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp w.2
    have hnode : node i = w := Subtype.ext hi
    rw [← hnode]
    exact hroot i
  exact ⟨hcard, hzero, hconnected⟩

end LPPDifferentiability
