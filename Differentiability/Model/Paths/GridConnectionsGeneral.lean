/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.GridFineGeneral
public import Differentiability.Model.Paths.GridCoarseGeneralCost
import Mathlib.Tactic

/-! # The per-vertex clause of the good event, general weights

The per-vertex clause of the good event `Gγ`, for general weights, is Lemma 5.7 (i) of the
differentiability preprint. The coarse good event is (5.26) of the differentiability preprint, with
items (C3) and (C6) of Appendix B.

`grid_det_general_named` holds the per-vertex clause at every scale at once, on `Egeo`, with the
four clauses of the staircase event and the coarse good events. It splits on the scale. A fine scale
is `grid_fine_general`. A coarse scale is `grid_coarse_general`, at the bin `h = ⌊r(u) / w⌋`, with
the crossing and heavy-vertex witness of the coarse good event. `grid_det_general` states the same
result with the three definitions unfolded.
-/

@[expose] public section

namespace LPPDifferentiability

/-- One connecting path of the per-vertex clause: from `z₀` to `z₁`, with both defects at most
`cost` and every vertex within `spread` of the transverse coordinate of `u`. -/
def GridConnection (ω : Environment) (a G0 dl dr cost spread : ℝ) (u z₀ z₁ : Lattice) : Prop :=
  ∃ (D : ℕ × ℕ) (y : Path z₀ D),
    z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
    G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
        pathWeight ω y ≤ cost ∧
    G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
        pathWeight ω y ≤ cost ∧
    ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) -
        ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤ spread

/-- The coarse good event at the grid interval `[I, I + l]` and the bin `h` of scale `j`:
for some block centre (index `N ≤ j²`) the crossing event and the heavy-vertex event hold. -/
def CoarseGoodAt (ω : Environment) (a G0 K cstar : ℝ) (mk k j : ℕ) (I h : ℤ) : Prop :=
  let w : ℕ := 2 ^ (k - j)
  let l : ℕ := 2 ^ (mk - 4 * j - 1)
  let m' : ℕ := ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊
  ∃ N : ℕ, 1 ≤ N ∧ N ≤ j ^ 2 ∧ ∃ c : Lattice,
    |(1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ) - ((h : ℝ) * (w : ℝ) + 30 * (N : ℝ) * (w : ℝ))| ≤
      1 / 2 ∧
    (∃ (x₀ : Lattice) (d : ℕ × ℕ) (x : Path x₀ d),
      x₀.1 + x₀.2 = I + (m' : ℤ) ∧ d.1 + d.2 = l - 2 * m' ∧
      (∀ i, |(1 - a) * ((x.vertex i).1 : ℝ) - a * ((x.vertex i).2 : ℝ) -
        ((1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ))| ≤ 8 * (w : ℝ)) ∧
      G0 * ((l - 2 * m' : ℕ) : ℝ) - K * (w : ℝ) < pathWeight ω x) ∧
    (∀ z : Lattice, I + (m' : ℤ) ≤ z.1 + z.2 → z.1 + z.2 ≤ I + (l : ℤ) - (m' : ℤ) →
      |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - ((1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ))| ≤
        8 * (w : ℝ) → ω z ≤ (w : ℝ))

/-- The per-vertex clause of the good event `Gγ`. -/
def GridVertexClause (ω : Environment) (T t a G0 dl dr C₁ A R : ℝ) (k J : ℕ) (m : ℕ → ℕ)
    (reach reachBack : Environment → ℝ → Lattice → Set Lattice) : Prop :=
  let gf : Lattice → ℕ → Lattice := fun u s =>
    GreedyAttachment.vertex u a {y | (reach ω T y).Finite} s
  let gb : Lattice → ℕ → Lattice := fun u s =>
    -GreedyAttachment.vertex (-u) a {y | ω (-y) < -T ∨ (reachBack ω T (-y)).Finite} s
  ∀ u : Lattice, |((u.1 + u.2 : ℤ) : ℝ)| ≤ A * 2 ^ m k →
    |(1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)| ≤ R * 2 ^ k →
    ∀ j : ℕ, J ≤ j → j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
    ∀ I : ℤ, ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ m k →
    ((-T ≤ ω u ∧ ¬ (reachBack ω T u).Finite) →
      (⌊((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (m k - 4 * J - 1) : ℕ) : ℝ)⌋ - 1) *
        ((2 ^ (m k - 4 * J - 1) : ℕ) : ℤ) ≤ I →
      I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ≤ u.1 + u.2 →
      ∀ z₀ z₁ : Lattice, z₀ = gb u (u.1 + u.2 - I).toNat →
        z₁ = gb u (u.1 + u.2 - (I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ))).toNat →
      GridConnection ω a G0 dl dr (C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * t)
        (C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ))) u z₀ z₁) ∧
    (¬ (reach ω T u).Finite →
      u.1 + u.2 ≤ I →
      I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ≤
        (⌈((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (m k - 4 * J - 1) : ℕ) : ℝ)⌉ + 1) *
          ((2 ^ (m k - 4 * J - 1) : ℕ) : ℤ) →
      ∀ z₀ z₁ : Lattice, z₀ = gf u (I - (u.1 + u.2)).toNat →
        z₁ = gf u (I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) - (u.1 + u.2)).toNat →
      GridConnection ω a G0 dl dr (C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * t)
        (C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ))) u z₀ z₁)

/-- Unfolding of `GridConnection`. -/
theorem gridConnection_iff (ω : Environment) (a G0 dl dr cost spread : ℝ) (u z₀ z₁ : Lattice) :
    GridConnection ω a G0 dl dr cost spread u z₀ z₁ ↔
    ∃ (D : ℕ × ℕ) (y : Path z₀ D),
      z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
      G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
          pathWeight ω y ≤ cost ∧
      G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
          pathWeight ω y ≤ cost ∧
      ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) -
          ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤ spread := Iff.rfl

/-- Unfolding of `CoarseGoodAt`. -/
theorem coarseGoodAt_iff (ω : Environment) (a G0 K cstar : ℝ) (mk k j : ℕ) (I h : ℤ) :
    CoarseGoodAt ω a G0 K cstar mk k j I h ↔
  (let w : ℕ := 2 ^ (k - j)
    let l : ℕ := 2 ^ (mk - 4 * j - 1)
    let m' : ℕ := ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊
    ∃ N : ℕ, 1 ≤ N ∧ N ≤ j ^ 2 ∧ ∃ c : Lattice,
      |(1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ) - ((h : ℝ) * (w : ℝ) + 30 * (N : ℝ) * (w : ℝ))| ≤
        1 / 2 ∧
      (∃ (x₀ : Lattice) (d : ℕ × ℕ) (x : Path x₀ d),
        x₀.1 + x₀.2 = I + (m' : ℤ) ∧ d.1 + d.2 = l - 2 * m' ∧
        (∀ i, |(1 - a) * ((x.vertex i).1 : ℝ) - a * ((x.vertex i).2 : ℝ) -
          ((1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ))| ≤ 8 * (w : ℝ)) ∧
        G0 * ((l - 2 * m' : ℕ) : ℝ) - K * (w : ℝ) < pathWeight ω x) ∧
      (∀ z : Lattice, I + (m' : ℤ) ≤ z.1 + z.2 → z.1 + z.2 ≤ I + (l : ℤ) - (m' : ℤ) →
        |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - ((1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ))| ≤
          8 * (w : ℝ) → ω z ≤ (w : ℝ))) := Iff.rfl

/-- Unfolding of `GridVertexClause`. -/
theorem gridVertexClause_iff (ω : Environment) (T t a G0 dl dr C₁ A R : ℝ) (k J : ℕ) (m : ℕ → ℕ)
    (reach reachBack : Environment → ℝ → Lattice → Set Lattice) :
    GridVertexClause ω T t a G0 dl dr C₁ A R k J m reach reachBack ↔
  (let gf : Lattice → ℕ → Lattice := fun u s =>
      GreedyAttachment.vertex u a {y | (reach ω T y).Finite} s
    let gb : Lattice → ℕ → Lattice := fun u s =>
      -GreedyAttachment.vertex (-u) a {y | ω (-y) < -T ∨ (reachBack ω T (-y)).Finite} s
    ∀ u : Lattice, |((u.1 + u.2 : ℤ) : ℝ)| ≤ A * 2 ^ m k →
      |(1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)| ≤ R * 2 ^ k →
      ∀ j : ℕ, J ≤ j → j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
      ∀ I : ℤ, ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ m k →
      ((-T ≤ ω u ∧ ¬ (reachBack ω T u).Finite) →
        (⌊((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (m k - 4 * J - 1) : ℕ) : ℝ)⌋ - 1) *
          ((2 ^ (m k - 4 * J - 1) : ℕ) : ℤ) ≤ I →
        I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ≤ u.1 + u.2 →
        ∀ z₀ z₁ : Lattice, z₀ = gb u (u.1 + u.2 - I).toNat →
          z₁ = gb u (u.1 + u.2 - (I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ))).toNat →
        GridConnection ω a G0 dl dr (C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * t)
          (C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ))) u z₀ z₁) ∧
      (¬ (reach ω T u).Finite →
        u.1 + u.2 ≤ I →
        I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ≤
          (⌈((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (m k - 4 * J - 1) : ℕ) : ℝ)⌉ + 1) *
            ((2 ^ (m k - 4 * J - 1) : ℕ) : ℤ) →
        ∀ z₀ z₁ : Lattice, z₀ = gf u (I - (u.1 + u.2)).toNat →
          z₁ = gf u (I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) - (u.1 + u.2)).toNat →
        GridConnection ω a G0 dl dr (C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * t)
          (C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ))) u z₀ z₁)) := Iff.rfl

/-- **The per-vertex clause of `Gγ`, general weights.** The clause as
`GridVertexClause`, on `Egeo`, the staircase event and the coarse good events. -/
theorem grid_det_general_named
    (ω : Environment) (T t a G0 dl dr K Cm cstar C₁ A R : ℝ) (m1 K1 k J : ℕ) (m : ℕ → ℕ) :
  let θ₁ : ℝ := min a (1 - a) / 5
  let reach : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
    {y | ∃ (d : ℕ × ℕ) (q : Path z d), z + ((d.1 : ℤ), (d.2 : ℤ)) = y ∧
      ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
  let reachBack : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
    {y | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = z ∧
      ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
  let Ntr : ℕ := K1 * (2 * m1 ^ 2 + 1) ^ 2
  let W0 : ℕ := Ntr + 1
  let L : ℕ := ⌈4 * ((W0 : ℝ) + 2) / θ₁⌉₊
  let r0 : ℕ := K1 * (2 * L + 1) + Ntr
  let D1 : ℕ := ⌊2 * (W0 : ℝ) / θ₁⌋₊ + 4 * W0 + 2 * r0 + 2 * L + 8
  let d0 : ℕ := D1 + 2 * m1 ^ 2
  let c0 : ℕ := W0 + 2 * L + 1
  let collar : Set Lattice → ℕ → Set Lattice := fun Q c =>
    {z | ∃ y ∈ Q, |z.1 - y.1| + |z.2 - y.2| ≤ (c : ℤ)}
  let Egeo : Environment → ℝ → Set Lattice → Prop := fun ω T Q =>
    (¬ ∃ f : Fin (K1 + 1) → Lattice, Function.Injective f ∧
        (∀ i, f i ∈ collar Q (c0 + m1 ^ 2) ∧ ω (f i) < -T) ∧
        ∀ i : Fin (K1 + 1), 0 < i.val → ∃ j : Fin (K1 + 1), j.val < i.val ∧
          |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ d0) ∧
    ∀ z ∈ collar Q c0,
      ((reach ω T z).Finite → (reach ω T z).ncard < m1 ^ 2) ∧
      ((reachBack ω T z).Finite → (reachBack ω T z).ncard < m1 ^ 2)
  let Qk : Set Lattice :=
    {z | |((z.1 + z.2 : ℤ) : ℝ)| ≤ (A + 5) * (2 : ℝ) ^ m k ∧
      |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ (R + 2 * C₁ + 10) * (2 : ℝ) ^ k}
  let Nl : ℝ := 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k
  let Vb : Set Lattice := {y | (reach ω T y).Finite}
  let Wb : Set Lattice := {y | ω (-y) < -T ∨ (reachBack ω T (-y)).Finite}
  0 < a → a < 1 → 1 ≤ m1 → 1 ≤ K1 → 1 ≤ J →
  0 ≤ t → cstar = 50 / min a (1 - a) → 1 ≤ K → |dl| ≤ K → |dr| ≤ K → 0 ≤ Cm → 0 ≤ G0 + 2 * Cm →
  8 * cstar * (G0 + 2 * Cm) + 2 * K + 2 * (r0 : ℝ) + 3 * cstar + 1 ≤ C₁ →
  ⌈((m k : ℝ) - 1) / 4⌉₊ ≤ k →
  4 * ((W0 : ℝ) + (r0 : ℝ) + (L : ℝ)) ≤ ((2 ^ (k - ⌈((m k : ℝ) - 1) / 4⌉₊) : ℕ) : ℝ) →
  2 * (W0 : ℝ) * K + 4 * (r0 : ℝ) * Cm ≤ ((2 ^ (k - ⌈((m k : ℝ) - 1) / 4⌉₊) : ℕ) : ℝ) →
  Egeo ω T Qk →
  (∀ (u : Lattice) (i n : ℕ), (n : ℝ) ≤ Nl →
    (∀ s, s ≤ i + n → GreedyAttachment.vertex u a Vb s ∈ Qk) →
    (∀ s, s < n → -T ≤ ω (GreedyAttachment.vertex u a Vb (i + s))) →
    -2 * Cm * (n : ℝ) - t / 2 ≤
      ∑ s ∈ Finset.range n, ω (GreedyAttachment.vertex u a Vb (i + s))) →
  (∀ (u : Lattice) (i n : ℕ), (n : ℝ) ≤ Nl →
    (∀ s, s ≤ i + n → -GreedyAttachment.vertex (-u) a Wb s ∈ Qk) →
    (∀ s, s < n → -T ≤ ω (-GreedyAttachment.vertex (-u) a Wb (i + 1 + s))) →
    -2 * Cm * (n : ℝ) - t / 2 ≤
      ∑ s ∈ Finset.range n, ω (-GreedyAttachment.vertex (-u) a Wb (i + 1 + s))) →
  (∀ z v : Lattice, z.1 ≤ v.1 → z.2 ≤ v.2 →
    let n : ℕ := (v.1 - z.1 + (v.2 - z.2)).toNat
    let q : ℝ := ((v.1 - z.1 : ℤ) : ℝ) / (n : ℝ)
    let x : ℕ → Lattice := GreedyAttachment.vertex z q Vb
    let e : ℕ × ℕ := ((v.1 - (x (n - L)).1).toNat, (v.2 - (x (n - L)).2).toNat)
    L ≤ n → (n : ℝ) ≤ Nl → (x (n - L)).1 ≤ v.1 → (x (n - L)).2 ≤ v.2 →
    (∀ s, s ≤ n - L → x s ∈ Qk) →
    (∀ i : Fin (e.1 + e.2 + 1), (horizontalFirst (x (n - L)) e).vertex i ∈ Qk) →
    (∀ s, s < n - L → -T ≤ ω (x s)) →
    (∀ i : Fin (e.1 + e.2 + 1), i.val < e.1 + e.2 →
      -T ≤ ω ((horizontalFirst (x (n - L)) e).vertex i)) →
    -2 * Cm * (n : ℝ) - t / 2 ≤
      (∑ s ∈ Finset.range (n - L), ω (x s)) +
        pathWeight ω (horizontalFirst (x (n - L)) e)) →
  (∀ (z u : Lattice) (Λ : ℤ) (n : ℕ), z.1 + z.2 < Λ →
    ((Λ - (z.1 + z.2) : ℤ) : ℝ) ≤ Nl → (n : ℝ) ≤ Nl → u ∈ Qk →
    let q : ℝ := ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) - 2 * (W0 : ℝ) - 3 +
      a * (Λ : ℝ) - (z.1 : ℝ)) / ((Λ - (z.1 + z.2) : ℤ) : ℝ)
    (∀ s, s ≤ n → GreedyAttachment.vertex z q Vb s ∈ Qk) →
    (∀ s, s < n → -T ≤ ω (GreedyAttachment.vertex z q Vb s)) →
    -2 * Cm * (n : ℝ) - t / 2 ≤
      ∑ s ∈ Finset.range n, ω (GreedyAttachment.vertex z q Vb s)) →
  (∀ j : ℕ, J ≤ j → j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
    8 * cstar * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) ≤ ((2 ^ (m k - 4 * j - 1) : ℕ) : ℝ) →
    ∀ I : ℤ, ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ m k →
    ∀ h : ℤ, (h : ℝ) * ((2 ^ (k - j) : ℕ) : ℝ) ≤ R * 2 ^ k →
      -(R * 2 ^ k) < ((h : ℝ) + 1) * ((2 ^ (k - j) : ℕ) : ℝ) →
    CoarseGoodAt ω a G0 K cstar (m k) k j I h) →
  GridVertexClause ω T t a G0 dl dr C₁ A R k J m reach reachBack := by
  intro _ _ _ _ W0 _ r0 _ _ _ _ _ _ _ _ _ ha0 ha1 hm1 hK1 hJ ht hcs hK hdl hdr hCm hGC hC hjk hWL hWK
    hEg hE1 hE2 hE3 hE4 hcoarse
  -- scalar facts needed to call the two pieces
  have hθ : 0 < min a (1 - a) := lt_min ha0 (by linarith only [ha1])
  have hcs0 : 0 ≤ cstar := by
    rw [hcs]
    exact div_nonneg (by norm_num) hθ.le
  have hr0 : (0 : ℝ) ≤ (r0 : ℝ) := Nat.cast_nonneg _
  have hr0Cm : 0 ≤ (r0 : ℝ) * Cm := mul_nonneg hr0 hCm
  have hC1f : 8 * cstar * (G0 + 2 * Cm) + 1 ≤ C₁ := by
    linarith only [hC, hK, hr0, hcs0]
  have hWKf : 2 * (W0 : ℝ) * K ≤ ((2 ^ (k - ⌈((m k : ℝ) - 1) / 4⌉₊) : ℕ) : ℝ) := by
    linarith only [hWK, hr0Cm]
  -- the bin of a real number
  have bin : ∀ ρ W : ℝ, 0 < W → ∃ h : ℤ, (h : ℝ) * W ≤ ρ ∧ ρ < ((h : ℝ) + 1) * W := by
    intro ρ W hW
    refine ⟨⌊ρ / W⌋, ?_, ?_⟩
    · have hfl := Int.floor_le (ρ / W)
      rwa [le_div_iff₀ hW] at hfl
    · have hfl := Int.lt_floor_add_one (ρ / W)
      rwa [div_lt_iff₀ hW] at hfl
  unfold GridVertexClause
  intro _ _ u hu1 hu2 j hJj hjj I hdiv hI
  rcases lt_or_ge ((2 ^ (m k - 4 * j - 1) : ℕ) : ℝ)
      (8 * cstar * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ))) with hfine | hcoarse'
  · -- fine scale
    exact grid_fine_general ω T t a G0 dl dr K Cm cstar C₁ A R m1 K1 k J m ha0 ha1 hm1 hK1 hJ ht
      hcs0 hK hdl hdr hGC hC1f hjk hWKf hEg hE1 hE2 u hu1 hu2 j hJj hjj hfine I hdiv hI
  · -- coarse scale: the bin of r(u), then the witness of the coarse good event
    have hw0 : (0 : ℝ) < ((2 ^ (k - j) : ℕ) : ℝ) := by positivity
    obtain ⟨h, hh1, hh2⟩ := bin ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)) ((2 ^ (k - j) : ℕ) : ℝ) hw0
    have hρ := abs_le.mp hu2
    have hb1 : (h : ℝ) * ((2 ^ (k - j) : ℕ) : ℝ) ≤ R * 2 ^ k := by linarith only [hρ.2, hh1]
    have hb2 : -(R * 2 ^ k) < ((h : ℝ) + 1) * ((2 ^ (k - j) : ℕ) : ℝ) := by linarith only [hρ.1, hh2]
    have hgood := hcoarse j hJj hjj hcoarse' I hdiv hI h hb1 hb2
    obtain ⟨N, hN1, hN2, c, hc, ⟨x₀, d, x, hx₀, hd, hxloc, hxw⟩, hH⟩ := hgood
    exact grid_coarse_general ω T t a G0 dl dr K Cm cstar C₁ A R m1 K1 k J m ha0 ha1 hm1 hK1 hJ ht
      hcs hdl hdr hCm hGC hC hjk hWL hWK hEg hE1 hE2 hE3 hE4 u hu1 hu2 j hJj hjj hcoarse' I hdiv hI
      h hh1 hh2 N hN1 hN2 c hc x₀ d x hx₀ hd hxloc hxw hH

/-- **The per-vertex clause of `Gγ`, fully unfolded**: `grid_det_general_named` with
`GridConnection`, `CoarseGoodAt` and `GridVertexClause` replaced by their bodies. -/
theorem grid_det_general
    (ω : Environment) (T t a G0 dl dr K Cm cstar C₁ A R : ℝ) (m1 K1 k J : ℕ) (m : ℕ → ℕ) :
  let θ₁ : ℝ := min a (1 - a) / 5
  let reach : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
    {y | ∃ (d : ℕ × ℕ) (q : Path z d), z + ((d.1 : ℤ), (d.2 : ℤ)) = y ∧
      ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
  let reachBack : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
    {y | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = z ∧
      ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
  let Ntr : ℕ := K1 * (2 * m1 ^ 2 + 1) ^ 2
  let W0 : ℕ := Ntr + 1
  let L : ℕ := ⌈4 * ((W0 : ℝ) + 2) / θ₁⌉₊
  let r0 : ℕ := K1 * (2 * L + 1) + Ntr
  let D1 : ℕ := ⌊2 * (W0 : ℝ) / θ₁⌋₊ + 4 * W0 + 2 * r0 + 2 * L + 8
  let d0 : ℕ := D1 + 2 * m1 ^ 2
  let c0 : ℕ := W0 + 2 * L + 1
  let collar : Set Lattice → ℕ → Set Lattice := fun Q c =>
    {z | ∃ y ∈ Q, |z.1 - y.1| + |z.2 - y.2| ≤ (c : ℤ)}
  let Egeo : Environment → ℝ → Set Lattice → Prop := fun ω T Q =>
    (¬ ∃ f : Fin (K1 + 1) → Lattice, Function.Injective f ∧
        (∀ i, f i ∈ collar Q (c0 + m1 ^ 2) ∧ ω (f i) < -T) ∧
        ∀ i : Fin (K1 + 1), 0 < i.val → ∃ j : Fin (K1 + 1), j.val < i.val ∧
          |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ d0) ∧
    ∀ z ∈ collar Q c0,
      ((reach ω T z).Finite → (reach ω T z).ncard < m1 ^ 2) ∧
      ((reachBack ω T z).Finite → (reachBack ω T z).ncard < m1 ^ 2)
  let Qk : Set Lattice :=
    {z | |((z.1 + z.2 : ℤ) : ℝ)| ≤ (A + 5) * (2 : ℝ) ^ m k ∧
      |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ (R + 2 * C₁ + 10) * (2 : ℝ) ^ k}
  let Nl : ℝ := 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k
  let Vb : Set Lattice := {y | (reach ω T y).Finite}
  let Wb : Set Lattice := {y | ω (-y) < -T ∨ (reachBack ω T (-y)).Finite}
  let gf : Lattice → ℕ → Lattice := fun u s =>
    GreedyAttachment.vertex u a {y | (reach ω T y).Finite} s
  let gb : Lattice → ℕ → Lattice := fun u s =>
    -GreedyAttachment.vertex (-u) a {y | ω (-y) < -T ∨ (reachBack ω T (-y)).Finite} s
  0 < a → a < 1 → 1 ≤ m1 → 1 ≤ K1 → 1 ≤ J →
  0 ≤ t → cstar = 50 / min a (1 - a) → 1 ≤ K → |dl| ≤ K → |dr| ≤ K → 0 ≤ Cm → 0 ≤ G0 + 2 * Cm →
  8 * cstar * (G0 + 2 * Cm) + 2 * K + 2 * (r0 : ℝ) + 3 * cstar + 1 ≤ C₁ →
  ⌈((m k : ℝ) - 1) / 4⌉₊ ≤ k →
  4 * ((W0 : ℝ) + (r0 : ℝ) + (L : ℝ)) ≤ ((2 ^ (k - ⌈((m k : ℝ) - 1) / 4⌉₊) : ℕ) : ℝ) →
  2 * (W0 : ℝ) * K + 4 * (r0 : ℝ) * Cm ≤ ((2 ^ (k - ⌈((m k : ℝ) - 1) / 4⌉₊) : ℕ) : ℝ) →
  Egeo ω T Qk →
  (∀ (u : Lattice) (i n : ℕ), (n : ℝ) ≤ Nl →
    (∀ s, s ≤ i + n → GreedyAttachment.vertex u a Vb s ∈ Qk) →
    (∀ s, s < n → -T ≤ ω (GreedyAttachment.vertex u a Vb (i + s))) →
    -2 * Cm * (n : ℝ) - t / 2 ≤
      ∑ s ∈ Finset.range n, ω (GreedyAttachment.vertex u a Vb (i + s))) →
  (∀ (u : Lattice) (i n : ℕ), (n : ℝ) ≤ Nl →
    (∀ s, s ≤ i + n → -GreedyAttachment.vertex (-u) a Wb s ∈ Qk) →
    (∀ s, s < n → -T ≤ ω (-GreedyAttachment.vertex (-u) a Wb (i + 1 + s))) →
    -2 * Cm * (n : ℝ) - t / 2 ≤
      ∑ s ∈ Finset.range n, ω (-GreedyAttachment.vertex (-u) a Wb (i + 1 + s))) →
  (∀ z v : Lattice, z.1 ≤ v.1 → z.2 ≤ v.2 →
    let n : ℕ := (v.1 - z.1 + (v.2 - z.2)).toNat
    let q : ℝ := ((v.1 - z.1 : ℤ) : ℝ) / (n : ℝ)
    let x : ℕ → Lattice := GreedyAttachment.vertex z q Vb
    let e : ℕ × ℕ := ((v.1 - (x (n - L)).1).toNat, (v.2 - (x (n - L)).2).toNat)
    L ≤ n → (n : ℝ) ≤ Nl → (x (n - L)).1 ≤ v.1 → (x (n - L)).2 ≤ v.2 →
    (∀ s, s ≤ n - L → x s ∈ Qk) →
    (∀ i : Fin (e.1 + e.2 + 1), (horizontalFirst (x (n - L)) e).vertex i ∈ Qk) →
    (∀ s, s < n - L → -T ≤ ω (x s)) →
    (∀ i : Fin (e.1 + e.2 + 1), i.val < e.1 + e.2 →
      -T ≤ ω ((horizontalFirst (x (n - L)) e).vertex i)) →
    -2 * Cm * (n : ℝ) - t / 2 ≤
      (∑ s ∈ Finset.range (n - L), ω (x s)) +
        pathWeight ω (horizontalFirst (x (n - L)) e)) →
  (∀ (z u : Lattice) (Λ : ℤ) (n : ℕ), z.1 + z.2 < Λ →
    ((Λ - (z.1 + z.2) : ℤ) : ℝ) ≤ Nl → (n : ℝ) ≤ Nl → u ∈ Qk →
    let q : ℝ := ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) - 2 * (W0 : ℝ) - 3 +
      a * (Λ : ℝ) - (z.1 : ℝ)) / ((Λ - (z.1 + z.2) : ℤ) : ℝ)
    (∀ s, s ≤ n → GreedyAttachment.vertex z q Vb s ∈ Qk) →
    (∀ s, s < n → -T ≤ ω (GreedyAttachment.vertex z q Vb s)) →
    -2 * Cm * (n : ℝ) - t / 2 ≤
      ∑ s ∈ Finset.range n, ω (GreedyAttachment.vertex z q Vb s)) →
  (∀ j : ℕ, J ≤ j → j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
    8 * cstar * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) ≤ ((2 ^ (m k - 4 * j - 1) : ℕ) : ℝ) →
    ∀ I : ℤ, ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ m k →
    let w : ℕ := 2 ^ (k - j)
    let l : ℕ := 2 ^ (m k - 4 * j - 1)
    let m' : ℕ := ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊
    ∀ h : ℤ, (h : ℝ) * (w : ℝ) ≤ R * 2 ^ k → -(R * 2 ^ k) < ((h : ℝ) + 1) * (w : ℝ) →
    ∃ N : ℕ, 1 ≤ N ∧ N ≤ j ^ 2 ∧ ∃ c : Lattice,
      |(1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ) - ((h : ℝ) * (w : ℝ) + 30 * (N : ℝ) * (w : ℝ))| ≤
        1 / 2 ∧
      (∃ (x₀ : Lattice) (d : ℕ × ℕ) (x : Path x₀ d),
        x₀.1 + x₀.2 = I + (m' : ℤ) ∧ d.1 + d.2 = l - 2 * m' ∧
        (∀ i, |(1 - a) * ((x.vertex i).1 : ℝ) - a * ((x.vertex i).2 : ℝ) -
          ((1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ))| ≤ 8 * (w : ℝ)) ∧
        G0 * ((l - 2 * m' : ℕ) : ℝ) - K * (w : ℝ) < pathWeight ω x) ∧
      (∀ z : Lattice, I + (m' : ℤ) ≤ z.1 + z.2 → z.1 + z.2 ≤ I + (l : ℤ) - (m' : ℤ) →
        |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - ((1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ))| ≤
          8 * (w : ℝ) → ω z ≤ (w : ℝ))) →
  ∀ u : Lattice, |((u.1 + u.2 : ℤ) : ℝ)| ≤ A * 2 ^ m k →
    |(1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)| ≤ R * 2 ^ k →
    ∀ j : ℕ, J ≤ j → j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
    ∀ I : ℤ, ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ m k →
    ((-T ≤ ω u ∧ ¬ (reachBack ω T u).Finite) →
      (⌊((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (m k - 4 * J - 1) : ℕ) : ℝ)⌋ - 1) *
        ((2 ^ (m k - 4 * J - 1) : ℕ) : ℤ) ≤ I →
      I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ≤ u.1 + u.2 →
      ∀ z₀ z₁ : Lattice, z₀ = gb u (u.1 + u.2 - I).toNat →
        z₁ = gb u (u.1 + u.2 - (I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ))).toNat →
      ∃ (D : ℕ × ℕ) (y : Path z₀ D),
        z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
            pathWeight ω y ≤
          C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * t ∧
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
            pathWeight ω y ≤
          C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * t ∧
        ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) -
            ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤
          C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ))) ∧
    (¬ (reach ω T u).Finite →
      u.1 + u.2 ≤ I →
      I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ≤
        (⌈((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (m k - 4 * J - 1) : ℕ) : ℝ)⌉ + 1) *
          ((2 ^ (m k - 4 * J - 1) : ℕ) : ℤ) →
      ∀ z₀ z₁ : Lattice, z₀ = gf u (I - (u.1 + u.2)).toNat →
        z₁ = gf u (I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) - (u.1 + u.2)).toNat →
      ∃ (D : ℕ × ℕ) (y : Path z₀ D),
        z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
            pathWeight ω y ≤
          C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * t ∧
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
            pathWeight ω y ≤
          C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * t ∧
        ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) -
            ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤
          C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ))) := by
  intro _ reach reachBack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ha0 ha1 hm1 hK1 hJ ht hcs hK hdl hdr hCm hGC hC hjk
    hWL hWK hEg hE1 hE2 hE3 hE4 hcoarse
  have hmain := grid_det_general_named ω T t a G0 dl dr K Cm cstar C₁ A R m1 K1 k J m ha0 ha1 hm1 hK1 hJ ht hcs hK hdl hdr hCm hGC hC hjk hWL hWK hEg hE1 hE2 hE3 hE4
    (fun j hJj hjj hc I hdiv hI h hb1 hb2 =>
      (coarseGoodAt_iff ω a G0 K cstar (m k) k j I h).2
        (hcoarse j hJj hjj hc I hdiv hI h hb1 hb2))
  exact (gridVertexClause_iff ω T t a G0 dl dr C₁ A R k J m reach reachBack).1 hmain

end LPPDifferentiability
