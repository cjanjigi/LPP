/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.StageCuts
public import LPP_Foundations.Model.Animals.PathSets
public import Mathlib.Data.Nat.Find
public import Mathlib.Algebra.Order.Floor.Ring

/-! The maximal number of disjoint witnesses in a stage and its sum over stages. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

namespace Path

/-- The path `q` is the segment of `p` starting at time `k`, with matching vertices
through its terminal time. -/
def is_segment_at {d : ℕ × ℕ} (p : Path 0 d) (k : ℕ)
    {u : Lattice} {e : ℕ × ℕ} (q : Path u e) : Prop :=
  k + (e.1 + e.2) ≤ d.1 + d.2 ∧
    ∀ (i : Fin (e.1 + e.2 + 1)) (t : Fin (d.1 + d.2 + 1)),
      t.val = k + i.val → q.vertex i = p.vertex t

/-- Index of the block assigned to the stage starting at time `k`. -/
noncomputable def stageBlockIndex {d : ℕ × ℕ} (p : Path 0 d) (a : ℝ) (m : ℕ)
    (s : ℝ) (k : Fin (d.1 + d.2 + 1)) : Lattice :=
  (⌊(k.val : ℝ) / (m : ℝ)⌋, ⌊latticeTransverseCoordinate a (p.vertex k) / s⌋)

/-- The point on the block's bottom level with transverse coordinate in `(h*s-1,h*s]`. -/
noncomputable def stageBlockOrigin (a : ℝ) (m : ℕ) (s : ℝ) (b : Lattice) : Lattice :=
  let j : ℤ := ⌊(b.2 : ℝ) * s + a * ((b.1 * (m : ℤ) : ℤ) : ℝ)⌋
  (j, b.1 * (m : ℤ) - j)

/-- The vertices of the block with index `b`, including its top level. -/
def mem_stage_block (a : ℝ) (m : ℕ) (s : ℝ) (b z : Lattice) : Prop :=
  (b.1 : ℝ) * (m : ℝ) ≤ (z.1 : ℝ) + (z.2 : ℝ) ∧
    (z.1 : ℝ) + (z.2 : ℝ) ≤ (b.1 : ℝ) * (m : ℝ) + 3 * (m : ℝ) ∧
    |latticeTransverseCoordinate a z - (b.2 : ℝ) * s| ≤ 4 * s

/-- A witness for the block event is a path exceeding a supporting bound in the block
or a crossing above the characteristic-length threshold. -/
def is_stage_block_witness {u : Lattice} {e : ℕ × ℕ} (q : Path u e)
    (ω : Environment) (a : ℝ) (m : ℕ) (s η G0 dl dr K : ℝ) (b : Lattice) : Prop :=
  ((∀ i, mem_stage_block a m s b (q.vertex i)) ∧
    q.minimumSupportDefect a G0 dl dr ω < -(η * s)) ∨
  (u.1 + u.2 = (b.1 + 1) * (m : ℤ) ∧ e.1 + e.2 = m ∧
    (∀ i, |latticeTransverseCoordinate a (q.vertex i) -
      latticeTransverseCoordinate a (stageBlockOrigin a m s (b.1 + 1, b.2))| ≤ 8 * s) ∧
    G0 * (m : ℝ) - K * s < pathWeight ω q)

/-- There are `M` pairwise collected-disjoint witness segments in the stage. -/
def has_stage_witness_family {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (m : ℕ) (s η G0 dl dr K : ℝ) (k l : Fin (d.1 + d.2 + 1)) (M : ℕ) : Prop :=
  ∃ (time : Fin M → ℕ) (start : Fin M → Lattice) (disp : Fin M → ℕ × ℕ)
    (q : (j : Fin M) → Path (start j) (disp j)),
    (∀ j, k.val ≤ time j ∧ time j + ((disp j).1 + (disp j).2) ≤ l.val ∧
      p.is_segment_at (time j) (q j) ∧
      (q j).is_stage_block_witness ω a m s η G0 dl dr K (p.stageBlockIndex a m s k)) ∧
    (∀ j j', j ≠ j' → Disjoint (q j).collectedSites (q j').collectedSites)

/-- Maximum number of pairwise collected-disjoint witness segments in a stage.
A family of witnesses has size at most the stage length. -/
noncomputable def stageWitnessMultiplicity {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (m : ℕ) (s η G0 dl dr K : ℝ) (_hm : 0 < m) (_hs : 0 < s) (_hη : 0 < η)
    (k l : Fin (d.1 + d.2 + 1)) (_hkl : k ≤ l) : ℕ := by
  classical
  exact Nat.findGreatest (p.has_stage_witness_family ω a m s η G0 dl dr K k l) (l.val - k.val)

/-- A sequence of first cuts of a path, with a last entry for the possibly empty remainder. -/
def is_first_stage_decomposition {d : ℕ × ℕ} (p : Path 0 d)
    (a : ℝ) (m : ℕ) (s : ℝ) {N : ℕ} (cuts : Fin (N + 2) → Fin (d.1 + d.2 + 1)) : Prop :=
  let rho := fun t => latticeTransverseCoordinate a (p.vertex t)
  cuts 0 = 0 ∧ cuts (Fin.last (N + 1)) = Fin.last (d.1 + d.2) ∧
  Monotone cuts ∧
  (∀ i : Fin N,
    let k := cuts ⟨i.val, by omega⟩
    let l := cuts ⟨i.val + 1, by omega⟩
    k < l ∧ p.reaches_stage_cut a m s k l ∧
      ∀ t, k < t → t < l → t.val - k.val < 2 * m ∧ |rho t - rho k| < s) ∧
  (∀ t, cuts ⟨N, by omega⟩ < t →
    t.val - (cuts ⟨N, by omega⟩).val < 2 * m ∧ |rho t - rho (cuts ⟨N, by omega⟩)| < s)

/-- Sum of the maximal stage counts, with one summand for the final remainder. -/
noncomputable def totalWitnessMultiplicity {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (m : ℕ) (s η G0 dl dr K : ℝ) (hm : 0 < m) (hs : 0 < s) (hη : 0 < η) {N : ℕ}
    (cuts : Fin (N + 2) → Fin (d.1 + d.2 + 1))
    (hcuts : p.is_first_stage_decomposition a m s cuts) : ℕ :=
  ∑ i : Fin (N + 1), p.stageWitnessMultiplicity ω a m s η G0 dl dr K hm hs hη
    (cuts i.castSucc) (cuts i.succ) (hcuts.2.2.1 i.castSucc_le_succ)

end Path

end LPPDifferentiability
