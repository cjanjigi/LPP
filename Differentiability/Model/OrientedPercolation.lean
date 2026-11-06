/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Environment
public import LPP_Foundations.Frozen.Model.Path
public import Mathlib.Data.Int.ConditionallyCompleteOrder

/-!
# Shared definitions for the flat segment

These definitions are used by the flat-segment part of the differentiability proof (Section 2.3 of
the differentiability preprint). The top weight `M_top` of the weight law is treated as a 0/1 field.
The weights are shifted so that the top value is `1`, and the top sites are the sites whose shifted
weight equals `1`.

Each docstring states the plain-language meaning of its definition and names the passage of the
differentiability preprint that it corresponds to. Some objects are introduced only for the
construction in the proof and have no counterpart in the preprint; the section comment before the
black-block group says so for those objects.

The definitions have no proofs.
-/

@[expose] public section

namespace LPPDifferentiability

open Set

/-! ## Levels, open paths and reachable sets -/

/-- Level `n`: the sites `(z₁, z₂)` whose coordinate sum is `n`. Levels are the
diagonal lines along which the growth is measured. -/
def levelSet (n : ℤ) : Set Lattice := {z | z.1 + z.2 = n}

/-- An open path from `u` to `v`: some up-right path from `u` to `v` in which every
vertex after the starting site `u` lies in `O`. The starting site itself does not have
to lie in `O`. When the path has at least one step, its end `v` comes after the start,
so `v` lies in `O` too. This is the convention of the flat-segment results in Section 2.3 of
the differentiability preprint. -/
def OpenReach (O : Set Lattice) (u v : Lattice) : Prop :=
  ∃ d : ℕ × ℕ, u + ((d.1 : ℤ), (d.2 : ℤ)) = v ∧
    ∃ p : Path u d, ∀ i : Fin (d.1 + d.2), p.vertex i.succ ∈ O

/-- `B_n(S)`: the sites reached from some start in `S` by an open path of exactly
`n` steps. For `S` on level `m`, this set lies on level `m + n`. It is defined for
every set `S`, including infinite ones such as the antidiagonal half-line. -/
def openReachSet (O S : Set Lattice) (n : ℕ) : Set Lattice :=
  {v | ∃ u ∈ S, OpenReach O u v ∧ v.1 + v.2 = u.1 + u.2 + n}

/-- The largest first coordinate of a set of sites, as an integer supremum. When the
set is nonempty with first coordinates bounded above, this is the true maximum.
Otherwise it is `0`, Mathlib's convention for `sSup` on `ℤ`. -/
noncomputable def maxFirst (X : Set Lattice) : ℤ := sSup (Prod.fst '' X)

/-- The edge `a_n(S)`: the largest first coordinate of the sites reached from `S`
in `n` open steps. If that set is empty or unbounded above, the value is the `0` that
`maxFirst` gives in that case. -/
noncomputable def openEdge (O S : Set Lattice) (n : ℕ) : ℤ := maxFirst (openReachSet O S n)

/-! ## The antidiagonal half-line and the top field -/

/-- The antidiagonal half-line `Z̃₋ = {(-k, k) : k ≥ 0}`: the sites on level `0`
with first coordinate at most `0`. It is the starting set for the edge `a_n(Z̃₋)`.
Section 2.3 of the differentiability preprint does not define it. -/
def antidiagHalfLine : Set Lattice := {z | z.1 + z.2 = 0 ∧ z.1 ≤ 0}

/-- The block `F_m = {(k, -k) : 1 ≤ k ≤ m}`: the sites on level `0` with first
coordinate between `1` and `m`. The augmentation step does not add this block itself.
It adds a translate of it, `r + (0, T) + F_T`, which is the set `triangleTargets T r`. -/
def antidiagRightBlock (m : ℕ) : Set Lattice := {z | z.1 + z.2 = 0 ∧ 1 ≤ z.1 ∧ z.1 ≤ m}

/-- The top sites of an environment: the sites whose weight equals `1`. For the
shifted weights `w̄ = w - M_top + 1` in the proof of Theorem 2.2 of the differentiability
preprint, these are the
sites that carry the top weight `M_top`. -/
def topSites (ω : Environment) : Set Lattice := {z | ω z = 1}

/-- The 0/1 top field of an environment: `1` at the top sites and `0` elsewhere.
This is the indicator field `1{w_z = M_top}` of Section 2.3 of the differentiability
preprint, for the shifted weights. -/
noncomputable def topField (ω : Environment) : Environment :=
  fun z => if ω z = 1 then 1 else 0

/-- The half-line edge `a_n(Z̃₋)`: the edge of the open-path growth from the
antidiagonal half-line, using the top sites of `ω` as the open sites. The edge speed is
defined through the expectations of this edge: it is the infimum, over `n`, of
the expected edge `E a_{n+1}` divided by `n + 1`. The differentiability preprint does not define
the speed this way. Section 2.3 of the differentiability preprint takes the speed from the
literature, namely Durrett (1984) and the results it quotes. -/
noncomputable def halfLineEdge (ω : Environment) (n : ℕ) : ℤ :=
  openEdge (topSites ω) antidiagHalfLine n

/-! ## Black blocks, triangles and the augmented process

These objects belong to the part of the construction that cuts the lattice into square blocks
of side `N` and works through the blocks one at a time. Section 2.3 of the differentiability
preprint does not define them; they are listed here so that the later files share one definition. -/

/-- Block `z` at scale `N` is black when the following holds. Take any site `u` on the
level that lies `N` steps above the corner `N z` of the block, with `u` at or above that
corner. Take any site `v` that is `N` steps up-right of `u` and at least `c₁ N` steps to
the right of `u`. Then there is no open path from `u` to `v`, where `O` is the set of
open sites. Nothing bounds `u` from above, and the path is not restricted to the block. -/
def IsBlackBlock (O : Set Lattice) (N : ℕ) (c₁ : ℝ) (z : Lattice) : Prop :=
  ∀ u v : Lattice, ((N : ℤ) * z.1, (N : ℤ) * z.2) ≤ u → u ≤ v →
    (u.1 - (N : ℤ) * z.1) + (u.2 - (N : ℤ) * z.2) = N →
    (v.1 - u.1) + (v.2 - u.2) = N →
    c₁ * N ≤ ((v.1 - u.1 : ℤ) : ℝ) → ¬ OpenReach O u v

/-- A `T`-triangle at the site `r` for the environment `ω` and the constant `c₀`.
It asks for three things: the `T` sites directly above `r` have weight below the
top value `1`; the site to the right of `r` has weight in `[c₀, 1)`; and every
other site of the triangle, that is, every site `z` with `r₁ + 1 ≤ z₁` and `r₂ ≤ z₂`
whose total distance from the right neighbour `(r₁ + 1, r₂)` is at most `T - 1`, except
that right neighbour itself, has top value `1`. -/
def IsTriangle (ω : Environment) (T : ℕ) (c₀ : ℝ) (r : Lattice) : Prop :=
  (∀ i : ℕ, 1 ≤ i → i ≤ T → ω (r.1, r.2 + i) < 1) ∧
  (c₀ ≤ ω (r.1 + 1, r.2) ∧ ω (r.1 + 1, r.2) < 1) ∧
  ∀ z : Lattice, r.1 + 1 ≤ z.1 → r.2 ≤ z.2 →
    (z.1 - (r.1 + 1)) + (z.2 - r.2) ≤ (T : ℤ) - 1 → z ≠ (r.1 + 1, r.2) → ω z = 1

/-- The `T` sites added by a triangle at `r`: the translate `r + (0, T) + F_T`, where
`F_T` is `antidiagRightBlock T`. Concretely, these are the sites on the level
`r₁ + r₂ + T` with first coordinate from `r₁ + 1` to `r₁ + T`. -/
def triangleTargets (T : ℕ) (r : Lattice) : Set Lattice :=
  {z | z.1 + z.2 = r.1 + r.2 + T ∧ r.1 + 1 ≤ z.1 ∧ z.1 ≤ r.1 + T}

/-- The augmented process at the block ends `jT`, started from the set `S`. At each
block end, the next set is the set of top sites reached from the current set `X` in
`T` open steps. If fewer than `k` augmentations have been made, the current lowest
point `r = (maxFirst X, jT - maxFirst X)` lies in `X`, and there is a triangle at
`r`, the process also adds `triangleTargets T r` and counts one augmentation. The
output pairs the set at the given block index with the number of augmentations made
so far. -/
noncomputable def augmentedProcess (ω : Environment) (T : ℕ) (c₀ : ℝ) (S : Set Lattice)
    (k : ℕ) : ℕ → Set Lattice × ℕ
  | 0 => (S, 0)
  | j + 1 =>
    haveI := Classical.propDecidable
    let X := (augmentedProcess ω T c₀ S k j).1
    let K := (augmentedProcess ω T c₀ S k j).2
    let r : Lattice := (maxFirst X, (j : ℤ) * T - maxFirst X)
    if K < k ∧ r ∈ X ∧ IsTriangle ω T c₀ r then
      (openReachSet (topSites ω) X T ∪ triangleTargets T r, K + 1)
    else (openReachSet (topSites ω) X T, K)

end LPPDifferentiability
