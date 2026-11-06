/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.LastPassage
public import Martin2004.Model.ColumnPassage
public import LPP_Foundations.Model.Paths.Geometry
public import LPP_Foundations.Model.Paths.Level

@[expose] public section

/-!
# The shear comparison for paths (Martin (2004), equations (4.1)-(4.2))

Martin (2004), (4.1) and the argument after it, compares the last passage time `T(m, n)` with the
one-site-per-column passage time `T̃(m + n, n)` of the column model (`columnPassage`).
The shear `ψ(x, y) = (x + y, y)` sends a directed path from `0` to `(m, n)` (terminal site
excluded) to a path with exactly one site in each
of the columns `0, ..., m + n - 1`, with heights that do not decrease and stay between `0` and `n`.

This module proves the deterministic half of that argument. For every environment `ω`, the weight
of each directed path in `ω` equals the weight of its sheared image in the sheared environment
`z ↦ ω (z.1 - z.2, z.2)` (the inverse shear is applied to the environment, so that the image of the
site `v` of the path is read as the site `ψ v` of the sheared environment). Hence
`lastPassage ω 0 (m, n) ≤ columnPassage (sheared ω) (m + n) n`. The statement about the law of the
sheared environment is in the probability part of the library.
-/

open scoped BigOperators

namespace LPPDifferentiability

/-- Martin (2004), the argument after (4.1): the shear maps every directed path from `0` to
`(m, n)` into a one-site-per-column path in columns `0, ..., m + n - 1` with heights at most `n`, so
the weight of the path is at most `T̃(m + n, n)` of the sheared environment
`z ↦ ω (z.1 - z.2, z.2)`. Taking the largest path weight gives `T(m, n) ≤ T̃(m + n, n)` for the
sheared environment. -/
theorem lastPassage_le_columnPassage_shear (ω : Environment) (m n : ℕ) :
    lastPassage ω 0 (m, n) ≤
      columnPassage (fun z : Lattice => ω (z.1 - z.2, z.2)) (m + n) n := by
  classical
  unfold lastPassage
  refine Finset.max'_le _ _ _ fun w hw => ?_
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hw
  -- Every vertex of a path from `0` to `(m, n)` has height between `0` and `n`.
  have hbounds : ∀ i : Fin (m + n + 1), 0 ≤ (p.vertex i).2 ∧ (p.vertex i).2 ≤ (n : ℤ) :=
    fun i => by
      have h := p.vertex_mem_Icc i
      exact ⟨h.1.2, by simpa using h.2.2⟩
  have hlt : ∀ i : Fin (m + n), ((p.vertex i.castSucc).2).toNat < n + 1 := fun i => by
    have := (hbounds i.castSucc).2
    omega
  -- The heights of the non-terminal vertices form a one-site-per-column path.
  let y : Fin (m + n) → Fin (n + 1) := fun i => ⟨((p.vertex i.castSucc).2).toNat, hlt i⟩
  have hy : Monotone y := fun i j hij => by
    have h : (p.vertex i.castSucc).2 ≤ (p.vertex j.castSucc).2 :=
      p.snd_monotone (Fin.castSucc_le_castSucc_iff.mpr hij)
    show ((p.vertex i.castSucc).2).toNat ≤ ((p.vertex j.castSucc).2).toNat
    omega
  -- The vertex at local time `i` is the site `(i - y i, y i)`, since its level is `i`.
  have hsite : ∀ i : Fin (m + n),
      p.vertex i.castSucc = (((i : ℕ) : ℤ) - ((y i : ℕ) : ℤ), ((y i : ℕ) : ℤ)) := fun i => by
    have hl : (p.vertex i.castSucc).1 + (p.vertex i.castSucc).2 = ((i : ℕ) : ℤ) := by
      simpa using p.level i.castSucc
    have h0 := (hbounds i.castSucc).1
    have hyv : ((y i : ℕ) : ℤ) = (p.vertex i.castSucc).2 := by
      show (((p.vertex i.castSucc).2).toNat : ℤ) = _
      omega
    rw [hyv]
    refine Prod.ext ?_ rfl
    show (p.vertex i.castSucc).1 = ((i : ℕ) : ℤ) - (p.vertex i.castSucc).2
    omega
  -- So the weight of the path in `ω` is the weight of this one-site-per-column path in the
  -- sheared environment.
  have hsum : pathWeight ω p = ∑ i : Fin (m + n),
      (fun z : Lattice => ω (z.1 - z.2, z.2)) (((i : ℕ) : ℤ), ((y i : ℕ) : ℤ)) := by
    unfold pathWeight
    exact Finset.sum_congr rfl fun i _ => congrArg ω (hsite i)
  exact hsum.le.trans (sum_le_columnPassage (fun z : Lattice => ω (z.1 - z.2, z.2)) y hy)

end LPPDifferentiability
