/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.NorthBoundaryTail
public import LPP_Foundations.Model.Paths.FirstTopRow
import LPP_Foundations.Model.Paths.PrefixLocality
import LPP_Foundations.Model.LastPassage.Basic
import Mathlib.Data.Finset.Max

/-! A pathwise upper bound by the finite north-boundary exit maximum. -/

@[expose] public section

open LPP.Busemann LPPDifferentiability

namespace LPP.Busemann

/-- The modified north-boundary weight of any path is at most its exit maximum.
This is the upper half of a derived one-sided exit formula, using the
first-entry decomposition of GRS 1510.00859v2, Lemma 6.4. Equation (6.8)
defines the related two-boundary NE passage. -/
theorem north_boundary_pathWeight_le_exit_max
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (x : Lattice) (d : ℕ × ℕ)
    (p : LPPDifferentiability.Path x d) :
    let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
    let N : Environment := fun z =>
      if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
    pathWeight N p ≤
      (Finset.univ : Finset (Fin (d.1 + 1))).sup' Finset.univ_nonempty
        (fun k => lastPassage ω x (d.1 - k.val, d.2) +
          C (v - ((k.val : ℤ), 0)) v) := by
  let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
  let N : Environment := fun z =>
    if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
  let objective : Fin (d.1 + 1) → ℝ := fun k =>
    lastPassage ω x (d.1 - k.val, d.2) +
      C (v - ((k.val : ℤ), 0)) v
  change pathWeight N p ≤
    (Finset.univ : Finset (Fin (d.1 + 1))).sup' Finset.univ_nonempty objective
  classical
  -- The first visit to the top row gives the actual path split.
  obtain ⟨j, _, hjBefore, hjHeight⟩ := p.exists_first_top_row_vertex
  let e := p.splitDisplacement j
  have heLe : e ≤ d := p.splitDisplacement_le j
  have heFirstLe : e.1 ≤ d.1 := heLe.1
  have heHeight : e.2 = d.2 := hjHeight
  let k : Fin (d.1 + 1) := ⟨d.1 - e.1, by omega⟩
  have hkLe : k.val ≤ d.1 := by
    dsimp only [k]
    omega
  have heExit : e = (d.1 - k.val, d.2) := by
    apply Prod.ext
    · dsimp only [k]
      omega
    · exact heHeight
  have hremaining : d - e = (k.val, 0) := by
    apply Prod.ext
    · change d.1 - e.1 = k.val
      dsimp only [k]
    · change d.2 - e.2 = 0
      rw [heHeight]
      exact Nat.sub_self _
  have heDefinition : p.splitDisplacement j = e := rfl
  -- Recover the split vertex using the signed cast identities.
  have hvertex : p.vertex j = v - ((k.val : ℤ), 0) := by
    rw [p.split_vertex j, heDefinition, heExit]
    dsimp only [v]
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_sub]
      rw [Nat.cast_sub hkLe]
      omega
    · simp only [Prod.snd_add, Prod.snd_sub]
      omega
  -- Before the first top-row visit, the modified environment equals omega.
  have hprefixEnvironment :
      pathWeight N (p.prefixPath j) = pathWeight ω (p.prefixPath j) := by
    apply LPP.pathWeight_prefix_eq_of_eq_before N ω p j
    intro i hi
    have hiFirst : i.castSucc < j := by
      change i.castSucc.val < j.val
      simpa only [Fin.val_castSucc] using hi
    have hbelow := hjBefore i.castSucc hiFirst
    have hbelowTop : (p.vertex i.castSucc).2 < v.2 := by
      change (p.vertex i.castSucc).2 < x.2 + (d.2 : ℤ)
      exact hbelow
    have hrowNe : (p.vertex i.castSucc).2 ≠ v.2 := ne_of_lt hbelowTop
    simp [N, hrowNe]
  -- Bound the two pieces before rewriting their scalar endpoints.
  have hprefixBound :
      pathWeight N (p.prefixPath j) ≤ lastPassage ω x e := by
    calc
      pathWeight N (p.prefixPath j) = pathWeight ω (p.prefixPath j) :=
        hprefixEnvironment
      _ ≤ lastPassage ω x e := pathWeight_le_lastPassage ω (p.prefixPath j)
  have hsuffixBound :
      pathWeight N (p.suffix j) ≤ lastPassage N (p.vertex j) (d - e) :=
    pathWeight_le_lastPassage N (p.suffix j)
  have hsuffixCocycle :
      pathWeight N (p.suffix j) ≤ C (v - ((k.val : ℤ), 0)) v := by
    calc
      pathWeight N (p.suffix j) ≤ lastPassage N (p.vertex j) (d - e) :=
        hsuffixBound
      _ = C (v - ((k.val : ℤ), 0)) v := by
        rw [hvertex, hremaining]
        simpa only [N] using
          north_boundary_horizontal_passage_eq_cocycle ω C hC v k.val
  -- The path split counts the joining vertex only in the suffix.
  have hpathBound :
      pathWeight N p ≤ lastPassage ω x e + C (v - ((k.val : ℤ), 0)) v := by
    rw [pathWeight_split N p j]
    exact add_le_add hprefixBound hsuffixCocycle
  have hactualExit : pathWeight N p ≤ objective k := by
    simpa only [objective, heExit] using hpathBound
  -- The actual exit index is one of the finite indices in the stated maximum.
  have hbelowMaximum : objective k ≤
      (Finset.univ : Finset (Fin (d.1 + 1))).sup' Finset.univ_nonempty objective := by
    exact Finset.le_sup' (s := Finset.univ) (f := objective) (Finset.mem_univ k)
  exact hactualExit.trans hbelowMaximum

end LPP.Busemann
