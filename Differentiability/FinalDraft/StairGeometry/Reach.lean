/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Environment
public import LPP_Foundations.Frozen.Model.Path
public import LPP_Foundations.Model.Animals.Traversal
import LPP_Foundations.Model.Paths.HorizontalFirst
import LPP_Foundations.Model.Paths.Split
import Mathlib.Tactic

/-! Forward and backward reachability with terminal-excluded site weights. -/

@[expose] public section

namespace LPPDifferentiability.StairGeometry

/-- The forward reachable set, as in the statements below. -/
def reachSet (ω : Environment) (T : ℝ) (z : Lattice) : Set Lattice :=
  {y | ∃ (d : ℕ × ℕ) (q : Path z d), z + ((d.1 : ℤ), (d.2 : ℤ)) = y ∧
    ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}

/-- The backward reachable set, as in the statements below. -/
def reachBackSet (ω : Environment) (T : ℝ) (z : Lattice) : Set Lattice :=
  {y | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = z ∧
    ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}

private theorem vertex_mem_reach {ω : Environment} {T : ℝ} {z : Lattice} {d : ℕ × ℕ}
    (q : Path z d) (hg : ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i))
    (k : Fin (d.1 + d.2 + 1)) : q.vertex k ∈ reachSet ω T z := by
  refine ⟨q.splitDisplacement k, q.prefixPath k, (q.split_vertex k).symm, fun i hi => ?_⟩
  have hk := q.splitDisplacement_length k
  have hk2 := k.isLt
  exact hg ⟨i.val, by show i.val < _; omega⟩ (by show i.val < _; omega)

theorem reach_step {ω : Environment} {T : ℝ} {z y : Lattice} (hy : y ∈ reachSet ω T z)
    (hg : -T ≤ ω y) (e : ℕ × ℕ) (he : e = (1, 0) ∨ e = (0, 1)) :
    y + ((e.1 : ℤ), (e.2 : ℤ)) ∈ reachSet ω T z := by
  obtain ⟨d, q, rfl, hq⟩ := hy
  have he1 : e.1 + e.2 = 1 := by rcases he with rfl | rfl <;> rfl
  refine ⟨d + e, q.concat (horizontalFirst _ e), ?_, fun i hi => ?_⟩
  · apply Prod.ext <;> simp [add_assoc]
  · have hle : i.val ≤ d.1 + d.2 := by simp only [Prod.fst_add, Prod.snd_add] at hi; omega
    have hv : (q.concat (horizontalFirst _ e)).vertex i = q.vertex ⟨i.val, by omega⟩ :=
      Path.concat_vertex_left q (horizontalFirst _ e) ⟨i.val, by omega⟩
    rw [hv]
    by_cases h : i.val < d.1 + d.2
    · exact hq ⟨i.val, by omega⟩ h
    · have : (⟨i.val, by omega⟩ : Fin (d.1 + d.2 + 1)) = Fin.last _ := Fin.ext (by simp; omega)
      rw [this, q.finish]
      exact hg

private theorem vertex_mem_reachBack {ω : Environment} {T : ℝ} {z y : Lattice} {d : ℕ × ℕ}
    (q : Path y d) (hz : y + ((d.1 : ℤ), (d.2 : ℤ)) = z)
    (hg : ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i))
    (k : Fin (d.1 + d.2 + 1)) : q.vertex k ∈ reachBackSet ω T z := by
  have hle := q.splitDisplacement_le k
  refine ⟨d - q.splitDisplacement k, q.suffix k, ?_, fun i hi => ?_⟩
  · have h1 := q.splitDisplacement_fst_cast k
    have h2 := q.splitDisplacement_snd_cast k
    rw [← hz]
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Nat.cast_sub hle.1, Nat.cast_sub hle.2] <;> omega
  · have hl := q.suffix_length k
    have hk2 := k.isLt
    exact hg ⟨k.val + i.val, by show k.val + i.val < _; omega⟩ (by show k.val + i.val < _; omega)

theorem reachBack_step {ω : Environment} {T : ℝ} {z y : Lattice}
    (e : ℕ × ℕ) (he : e = (1, 0) ∨ e = (0, 1))
    (hy : y + ((e.1 : ℤ), (e.2 : ℤ)) ∈ reachBackSet ω T z) (hg : -T ≤ ω y) :
    y ∈ reachBackSet ω T z := by
  obtain ⟨d, q, hz, hq⟩ := hy
  have he1 : e.1 + e.2 = 1 := by rcases he with rfl | rfl <;> rfl
  refine ⟨e + d, (horizontalFirst y e).concat q, ?_, fun i hi => ?_⟩
  · rw [← hz]; apply Prod.ext <;> simp [add_assoc]
  · by_cases h0 : i.val = 0
    · have : i = 0 := Fin.ext h0
      rw [this, ((horizontalFirst y e).concat q).start]
      exact hg
    · simp only [Prod.fst_add, Prod.snd_add] at hi
      have hi' : i = ⟨e.1 + e.2 + (i.val - 1), by simp only [Prod.fst_add, Prod.snd_add]; omega⟩ :=
        Fin.ext (by show i.val = e.1 + e.2 + (i.val - 1); omega)
      have hv := Path.concat_vertex_right (horizontalFirst y e) q ⟨i.val - 1, by omega⟩
      rw [(congrArg ((horizontalFirst y e).concat q).vertex hi').trans hv]
      exact hq ⟨i.val - 1, by omega⟩ (by show i.val - 1 < _; omega)

/-- The length-zero path is available even when its only site is very bad. -/
theorem mem_reach_self (ω : Environment) (T : ℝ) (z : Lattice) : z ∈ reachSet ω T z :=
  ⟨(0, 0), horizontalFirst z (0, 0), by simp, fun _ hi => by omega⟩

/-- The length-zero path shows that the backward reachable set contains its target. -/
theorem mem_reachBack_self (ω : Environment) (T : ℝ) (z : Lattice) : z ∈ reachBackSet ω T z :=
  ⟨(0, 0), horizontalFirst z (0, 0), by simp, fun _ hi => by omega⟩

private theorem path_reachable_in {S : Finset Lattice} {u : Lattice} {d : ℕ × ℕ}
    (q : Path u d) (hS : ∀ i, q.vertex i ∈ S) :
    (nearestNeighborGraph.induce (S : Set Lattice)).Reachable
      ⟨q.vertex 0, hS 0⟩ ⟨q.vertex (Fin.last _), hS (Fin.last _)⟩ := by
  have hreach (n : ℕ) (hn : n ≤ d.1 + d.2) :
      (nearestNeighborGraph.induce (S : Set Lattice)).Reachable
        ⟨q.vertex 0, hS 0⟩ ⟨q.vertex ⟨n, by omega⟩, hS ⟨n, by omega⟩⟩ := by
    induction n with
    | zero => exact SimpleGraph.Reachable.rfl
    | succ n ih =>
      let i : Fin (d.1 + d.2) := ⟨n, by omega⟩
      apply (ih (by omega)).trans
      apply SimpleGraph.Adj.reachable
      change nearestNeighborGraph.Adj (q.vertex i.castSucc) (q.vertex i.succ)
      rcases q.step i with h | h <;> simp [nearestNeighborGraph, h]
  exact hreach _ le_rfl

/-- A finite forward reachable set is connected by the prefixes of its admissible paths. -/
theorem reach_connected {ω : Environment} {T : ℝ} {z : Lattice} {S : Finset Lattice}
    (hS : (S : Set Lattice) = reachSet ω T z) : IsConnectedAnimal S := by
  have hz : z ∈ (S : Set Lattice) := hS.symm ▸ mem_reach_self ω T z
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨⟨z, hz⟩, ?_⟩
  intro ⟨y, hy⟩
  have hy' : y ∈ reachSet ω T z := hS ▸ hy
  obtain ⟨d, q, hfinish, hgood⟩ := hy'
  have hvertices (i) : q.vertex i ∈ S := Finset.mem_coe.mp (hS.symm ▸ vertex_mem_reach q hgood i)
  have hp := path_reachable_in q hvertices
  have h0 : (⟨q.vertex 0, hvertices 0⟩ : (S : Set Lattice)) = ⟨z, hz⟩ := Subtype.ext q.start
  have h1 : (⟨q.vertex (Fin.last _), hvertices (Fin.last _)⟩ : (S : Set Lattice)) = ⟨y, hy⟩ :=
    Subtype.ext (q.finish.trans hfinish)
  rwa [h0, h1] at hp

/-- A finite backward reachable set is connected by the suffixes of its admissible paths. -/
theorem reachBack_connected {ω : Environment} {T : ℝ} {z : Lattice} {S : Finset Lattice}
    (hS : (S : Set Lattice) = reachBackSet ω T z) : IsConnectedAnimal S := by
  have hz : z ∈ (S : Set Lattice) := hS.symm ▸ mem_reachBack_self ω T z
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨⟨z, hz⟩, ?_⟩
  intro ⟨y, hy⟩
  have hy' : y ∈ reachBackSet ω T z := hS ▸ hy
  obtain ⟨d, q, hfinish, hgood⟩ := hy'
  have hvertices (i) : q.vertex i ∈ S :=
    Finset.mem_coe.mp (hS.symm ▸ vertex_mem_reachBack q hfinish hgood i)
  have hp := path_reachable_in q hvertices
  have h0 : (⟨q.vertex 0, hvertices 0⟩ : (S : Set Lattice)) = ⟨y, hy⟩ := Subtype.ext q.start
  have h1 : (⟨q.vertex (Fin.last _), hvertices (Fin.last _)⟩ : (S : Set Lattice)) = ⟨z, hz⟩ :=
    Subtype.ext (q.finish.trans hfinish)
  rw [h0, h1] at hp
  exact hp.symm

end LPPDifferentiability.StairGeometry
