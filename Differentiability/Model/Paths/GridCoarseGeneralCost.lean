/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.GridCoarseGeneralAssembly
import Mathlib.Tactic

/-! # The coarse scale of the general version of Lemma 5.7(i): path, cost and location

`grid_coarse_general` is the coarse-scale case of the per-vertex clause of the good event of the
general version of Lemma 5.7 (items (C2)-(C4) and (C6) of Section B.3): along the part of
`γ^u` below or above `u`, on the crossing-and-H witness of the coarse good event at the bin of
`r(u)`, the arrival path, the trimmed crossing, the greedy merge path and the tail of `γ^u`
form one admissible path from `γ^u(I)` to `γ^u(I + l)` whose two defects are at most
`C₁ j² w + 2t` (equation (B.11)) and whose vertices stay within `C₁ j² w` of `r(u)`.
-/

public section

namespace LPPDifferentiability
open GreedyAttachment (vertex deviation)

/-- **Coarse scale of the general version of Lemma 5.7(i).** -/
theorem grid_coarse_general
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
  0 ≤ t → cstar = 50 / min a (1 - a) → |dl| ≤ K → |dr| ≤ K → 0 ≤ Cm → 0 ≤ G0 + 2 * Cm →
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
  ∀ u : Lattice, |((u.1 + u.2 : ℤ) : ℝ)| ≤ A * 2 ^ m k →
    |(1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)| ≤ R * 2 ^ k →
    ∀ j : ℕ, J ≤ j → j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
    8 * cstar * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) ≤ ((2 ^ (m k - 4 * j - 1) : ℕ) : ℝ) →
    ∀ I : ℤ, ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ m k →
    let w : ℕ := 2 ^ (k - j)
    let l : ℕ := 2 ^ (m k - 4 * j - 1)
    let m' : ℕ := ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊
    ∀ h : ℤ, (h : ℝ) * (w : ℝ) ≤ (1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) →
      (1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) < ((h : ℝ) + 1) * (w : ℝ) →
    ∀ (N : ℕ), 1 ≤ N → N ≤ j ^ 2 → ∀ c : Lattice,
      |(1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ) - ((h : ℝ) * (w : ℝ) + 30 * (N : ℝ) * (w : ℝ))| ≤
        1 / 2 →
    ∀ (x₀ : Lattice) (d : ℕ × ℕ) (x : Path x₀ d),
      x₀.1 + x₀.2 = I + (m' : ℤ) → d.1 + d.2 = l - 2 * m' →
      (∀ i, |(1 - a) * ((x.vertex i).1 : ℝ) - a * ((x.vertex i).2 : ℝ) -
        ((1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ))| ≤ 8 * (w : ℝ)) →
      G0 * ((l - 2 * m' : ℕ) : ℝ) - K * (w : ℝ) < pathWeight ω x →
      (∀ z : Lattice, I + (m' : ℤ) ≤ z.1 + z.2 → z.1 + z.2 ≤ I + (l : ℤ) - (m' : ℤ) →
        |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - ((1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ))| ≤
          8 * (w : ℝ) → ω z ≤ (w : ℝ)) →
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
  intro θ₁ reach reachBack Ntr W0 L r0 D1 d0 c0 collar Egeo Qk Nl Vb Wb gf gb ha₀ ha₁ hm1 hK1 hJ
    ht hcs hdl hdr hCm hGC hC₁ hjk hw4 hwK hE hE1 hE2 hE3 hE4 u huA huR j hJj hjj hcoarse I _
    hIA w l m' h hh1 hh2 N hN1 hN2 c hc x₀ d x hx0 hd hxc hxW hH
  rw [show ((2 ^ (k - j) : ℕ) : ℝ) = (w : ℝ) from rfl,
    show ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) = (l : ℤ) from rfl]
  set ρ : ℝ := (1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) with hρ
  set P : ℝ := (j : ℝ) ^ 2 * (w : ℝ) with hP
  -- Constants of the direction and of the scale.
  obtain ⟨hθpos, hθle, h5a, h5b, -, hc100⟩ := coarse_direction_facts a cstar θ₁ rfl ha₀ ha₁ hcs
  have hwmin : ((2 ^ (k - ⌈((m k : ℝ) - 1) / 4⌉₊) : ℕ) : ℝ) ≤ (w : ℝ) := by
    exact Nat.cast_le.mpr (Nat.pow_le_pow_right (show 0 < 2 by norm_num)
      (show k - ⌈((m k : ℝ) - 1) / 4⌉₊ ≤ k - j by omega))
  have hW4 := hw4.trans hwmin
  have hWK := hwK.trans hwmin
  have hW01 : (1 : ℝ) ≤ W0 := by exact_mod_cast (show 1 ≤ Ntr + 1 by omega)
  have hr01 : (1 : ℝ) ≤ r0 := by
    have := Nat.mul_le_mul hK1 (show 1 ≤ 2 * L + 1 by omega)
    exact_mod_cast (show 1 ≤ K1 * (2 * L + 1) + Ntr by omega)
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hJ.trans hJj
  have hPw : (w : ℝ) ≤ P := le_mul_of_one_le_left (Nat.cast_nonneg w) (one_le_pow₀ hj1)
  have hP0 : 0 ≤ P := mul_nonneg (by positivity) (Nat.cast_nonneg w)
  have hcP : 100 * P ≤ cstar * P := mul_le_mul_of_nonneg_right hc100 hP0
  have hlR : 8 * cstar * P ≤ (l : ℝ) := hcoarse
  have hwW : 4 * W0 + 4 ≤ w := by
    have : ((4 * W0 + 4 : ℕ) : ℝ) ≤ (w : ℝ) := by push_cast; linarith only [hW4, hr01, hL0]
    exact_mod_cast this
  have hlw : w ≤ l := by
    have : (w : ℝ) ≤ l := by linarith only [hlR, hcP, hPw, hP0]
    exact_mod_cast this
  have hW0m : m1 ^ 2 ≤ W0 := by
    show m1 ^ 2 ≤ K1 * (2 * m1 ^ 2 + 1) ^ 2 + 1
    have h1 : m1 ^ 2 ≤ (2 * m1 ^ 2 + 1) ^ 2 := le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
    have h2 : (2 * m1 ^ 2 + 1) ^ 2 ≤ K1 * (2 * m1 ^ 2 + 1) ^ 2 := Nat.le_mul_of_pos_left _ hK1
    omega
  have hPk : P ≤ 2 * 2 ^ k := coarse_pow_bound j k (hjj.trans hjk)
  have hl2m : (l : ℝ) ≤ 2 ^ m k := by exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2m : (0 : ℝ) < 2 ^ m k := by positivity
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  obtain ⟨hIA1, hIA2⟩ := abs_le.mp hIA
  obtain ⟨huA1, huA2⟩ := abs_le.mp huA
  obtain ⟨huR1, huR2⟩ := abs_le.mp huR
  have hcC : cstar ≤ C₁ := by
    have hcG := mul_nonneg (by linarith only [hc100] : (0 : ℝ) ≤ cstar) hGC
    have hK0 := (abs_nonneg dl).trans hdl
    linarith only [hC₁, hcG, hK0, hr01, hc100]
  -- Region membership: levels between `I` (or `ℓ(u)`) and `I + l` (or `ℓ(u)`), and
  -- transverse coordinate within `c_* P` of `ρ`.
  have hQ : ∀ y : Lattice, (I ≤ y.1 + y.2 ∨ u.1 + u.2 ≤ y.1 + y.2) →
      (y.1 + y.2 ≤ I + l ∨ y.1 + y.2 ≤ u.1 + u.2) →
      |(1 - a) * (y.1 : ℝ) - a * (y.2 : ℝ) - ρ| ≤ cstar * P → y ∈ Qk := by
    intro y h1 h2 h3
    show |((y.1 + y.2 : ℤ) : ℝ)| ≤ (A + 5) * (2 : ℝ) ^ m k ∧
      |(1 - a) * (y.1 : ℝ) - a * (y.2 : ℝ)| ≤ (R + 2 * C₁ + 10) * (2 : ℝ) ^ k
    have hlo : -((A + 4) * 2 ^ m k) ≤ ((y.1 + y.2 : ℤ) : ℝ) := by
      rcases h1 with h1 | h1
      · have : (I : ℝ) ≤ ((y.1 + y.2 : ℤ) : ℝ) := by exact_mod_cast h1
        linarith only [this, hIA1]
      · have : ((u.1 + u.2 : ℤ) : ℝ) ≤ ((y.1 + y.2 : ℤ) : ℝ) := by exact_mod_cast h1
        linarith only [this, huA1, h2m]
    have hhi : ((y.1 + y.2 : ℤ) : ℝ) ≤ (A + 4) * 2 ^ m k + 2 ^ m k := by
      rcases h2 with h2 | h2
      · have : ((y.1 + y.2 : ℤ) : ℝ) ≤ (I : ℝ) + (l : ℝ) := by exact_mod_cast h2
        linarith only [this, hIA2, hl2m]
      · have : ((y.1 + y.2 : ℤ) : ℝ) ≤ ((u.1 + u.2 : ℤ) : ℝ) := by exact_mod_cast h2
        linarith only [this, huA2, h2m]
    have h4 := mul_le_mul_of_nonneg_left hPk (by linarith only [hc100] : (0 : ℝ) ≤ cstar)
    have h5 := mul_le_mul_of_nonneg_right hcC h2k.le
    obtain ⟨h31, h32⟩ := abs_le.mp h3
    exact ⟨abs_le.mpr ⟨by linarith only [hlo, h2m], by linarith only [hhi]⟩,
      abs_le.mpr ⟨by linarith only [h31, huR1, h4, h5, h2k],
        by linarith only [h32, huR2, h4, h5, h2k]⟩⟩
  have huQ : u ∈ Qk := hQ u (Or.inr le_rfl) (Or.inr le_rfl) (by
    show |ρ - ρ| ≤ cstar * P
    rw [sub_self, abs_zero]
    exact mul_nonneg (by linarith only [hc100]) hP0)
  have hEr : ∀ z ∈ collar Qk c0, ((reach ω T z).Finite → (reach ω T z).ncard < m1 ^ 2) ∧
      ((reachBack ω T z).Finite → (reachBack ω T z).ncard < m1 ^ 2) := by
    obtain ⟨-, h⟩ := hE
    exact h
  -- The four pieces along any segment `g` of `γ^u` over the interval.
  have key := coarse_four_piece_path ω T θ₁ m1 K1 Qk a t G0 dl dr K Cm cstar C₁ Nl ρ k j w l m' I
    rfl ha₀ ha₁ hm1 hK1 (hJ.trans hJj) (hjj.trans hjk) ht hcs hdl hdr hCm hGC hC₁ rfl rfl hcoarse
    hW4 hWK rfl hE hE3 hE4 u huQ hρ.symm (fun y h1 h2 h3 => hQ y (Or.inl h1) (Or.inl h2) h3) h
    hh1 hh2 N hN1 hN2 c hc x₀ d x hx0 hd hxc hxW hH
  refine ⟨fun hub _ hup z₀ z₁ hz₀ hz₁ => ?_, fun hnt hlo _ z₀ z₁ hz₀ hz₁ => ?_⟩
  · -- The part of `γ^u` below `u`.
    obtain ⟨hTu, hBu⟩ := hub
    obtain ⟨nB, hnB⟩ : ∃ nB : ℕ, (nB : ℤ) = u.1 + u.2 - I := ⟨(u.1 + u.2 - I).toNat, by omega⟩
    have hgbL : ∀ s, (gb u s).1 + (gb u s).2 = u.1 + u.2 - (s : ℤ) := fun s => by
      have h := GreedyAttachment.level (-u) a Wb s
      show (-(vertex (-u) a Wb s)).1 + (-(vertex (-u) a Wb s)).2 = _
      simp only [Prod.fst_neg, Prod.snd_neg] at h ⊢
      omega
    have hgbR : ∀ s, |(1 - a) * ((gb u s).1 : ℝ) - a * ((gb u s).2 : ℝ) - ρ| =
        |deviation (-u) a s (vertex (-u) a Wb s)| := fun s => by
      have he := GreedyAttachment.transverse_deviation_eq (-u) (vertex (-u) a Wb s) a a s
        (GreedyAttachment.level _ _ _ s)
      have : (1 - a) * ((gb u s).1 : ℝ) - a * ((gb u s).2 : ℝ) - ρ =
          -deviation (-u) a s (vertex (-u) a Wb s) := by
        rw [← he, hρ]
        show (1 - a) * (((-(vertex (-u) a Wb s)).1 : ℤ) : ℝ) -
          a * (((-(vertex (-u) a Wb s)).2 : ℤ) : ℝ) - ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)) = _
        simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
        ring
      rw [this, abs_neg]
    have hmarB : ∀ s, s ≤ nB → |deviation (-u) a s (vertex (-u) a Wb s)| ≤ (W0 : ℝ) + 1 →
        gb u s ∈ Qk := fun s hs hd => hQ (gb u s) (Or.inl (by have := hgbL s; omega))
          (Or.inr (by have := hgbL s; omega))
          (((hgbR s).trans_le hd).trans (by linarith only [hW4, hr01, hL0, hPw, hcP, hP0]))
    have hB := greedy_backward_in_region ω T θ₁ m1 K1 Qk hθpos hθle hm1 hK1 hE u huQ hTu hBu a
      (by linarith only [h5a, hθpos]) (by linarith only [h5b, hθpos]) nB hmarB
    have hB' : ∀ s, s ≤ nB → gb u s ∈ Qk ∧ -T ≤ ω (gb u s) ∧ ¬ (reachBack ω T (gb u s)).Finite ∧
        |deviation (-u) a s (vertex (-u) a Wb s)| ≤ (W0 : ℝ) := hB
    have hgbS : ∀ s, gb u s = gb u (s + 1) + (1, 0) ∨ gb u s = gb u (s + 1) + (0, 1) := fun s => by
      rcases GreedyAttachment.step (-u) a Wb s with h | h
      · left; show -vertex (-u) a Wb s = -vertex (-u) a Wb (s + 1) + (1, 0); rw [h]; abel
      · right; show -vertex (-u) a Wb s = -vertex (-u) a Wb (s + 1) + (0, 1); rw [h]; abel
    set g : ℕ → Lattice := fun s => gb u (nB - s)
    have hgs : ∀ s < nB, g (s + 1) = g s + (1, 0) ∨ g (s + 1) = g s + (0, 1) := fun s hs => by
      have h := hgbS (nB - (s + 1))
      rwa [show nB - (s + 1) + 1 = nB - s by omega] at h
    have hg0Q : g 0 ∈ Qk := (hB' nB le_rfl).1
    have hgt : ¬ (reach ω T (g 0)).Finite :=
      not_trapped_of_long_seq ω T m1 g nB hgs (fun s hs => (hB' _ (by omega)).2.1) (by omega)
        (hEr (g 0) (by
          show ∃ y ∈ Qk, |(g 0).1 - y.1| + |(g 0).2 - y.2| ≤ (c0 : ℤ)
          exact ⟨g 0, hg0Q, by simp⟩)).1
    obtain ⟨D, y, hD, h1, h2, h3⟩ := key g (fun s hs => hgs s (by omega))
      (fun s hs => by show (gb u (nB - s)).1 + (gb u (nB - s)).2 = _; have := hgbL (nB - s); omega)
      (fun s hs => (hgbR _).trans_le (hB' _ (by omega)).2.2.2) hgt (fun i n hin hn => by
        have h := hE2 u (nB - i - n) n hn (fun s hs => (hB' s (by omega)).1)
          (fun s hs => (hB' _ (by omega)).2.1)
        refine h.trans_eq ?_
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun s hs => ?_
        have := Finset.mem_range.mp hs
        show ω (gb u (nB - i - n + 1 + (n - 1 - s))) = ω (gb u (nB - (i + s)))
        congr 2
        omega)
    subst hz₀ hz₁
    rw [show (u.1 + u.2 - I).toNat = nB by omega,
      show (u.1 + u.2 - (I + (l : ℤ))).toNat = nB - l by omega]
    exact ⟨D, y, hD, h1, h2, h3⟩
  · -- The part of `γ^u` above `u`.
    obtain ⟨nA, hnA⟩ : ∃ nA : ℕ, (nA : ℤ) = I - (u.1 + u.2) := ⟨(I - (u.1 + u.2)).toNat, by omega⟩
    have hgfL : ∀ s, (gf u s).1 + (gf u s).2 = u.1 + u.2 + (s : ℤ) :=
      GreedyAttachment.level u a _
    have hgfR : ∀ s, |(1 - a) * ((gf u s).1 : ℝ) - a * ((gf u s).2 : ℝ) - ρ| =
        |deviation u a s (gf u s)| := fun s => by
      have he := GreedyAttachment.transverse_deviation_eq u (gf u s) a a s (hgfL s)
      rw [← he, hρ]
      congr 1
      ring
    have hmarF : ∀ s, s ≤ nA + l → |deviation u a s (gf u s)| ≤ (W0 : ℝ) + 1 → gf u s ∈ Qk :=
      fun s hs hd => hQ (gf u s) (Or.inr (by have := hgfL s; omega))
        (Or.inl (by have := hgfL s; omega))
        (((hgfR s).trans_le hd).trans (by linarith only [hW4, hr01, hL0, hPw, hcP, hP0]))
    have hF := greedy_forward_in_region ω T θ₁ m1 K1 Qk hθpos hθle hm1 hK1 hE u huQ hnt a
      (by linarith only [h5a, hθpos]) (by linarith only [h5b, hθpos]) (nA + l) hmarF
    have hF' : ∀ s, s ≤ nA + l → gf u s ∈ Qk ∧ ¬ (reach ω T (gf u s)).Finite ∧
        -T ≤ ω (gf u s) ∧ |deviation u a s (gf u s)| ≤ (W0 : ℝ) := hF
    set g : ℕ → Lattice := fun s => gf u (nA + s)
    obtain ⟨D, y, hD, h1, h2, h3⟩ := key g
      (fun s _ => GreedyAttachment.step u a _ (nA + s))
      (fun s hs => by show (gf u (nA + s)).1 + (gf u (nA + s)).2 = _; have := hgfL (nA + s); omega)
      (fun s hs => (hgfR _).trans_le (hF' _ (by omega)).2.2.2) (hF' nA (by omega)).2.1
      (fun i n hin hn => by
        have h := hE1 u (nA + i) n hn (fun s hs => (hF' s (by omega)).1)
          (fun s hs => (hF' _ (by omega)).2.2.1)
        refine h.trans_eq (Finset.sum_congr rfl fun s _ => ?_)
        show ω (gf u (nA + i + s)) = ω (gf u (nA + (i + s)))
        rw [Nat.add_assoc nA i s])
    subst hz₀ hz₁
    rw [show (I - (u.1 + u.2)).toNat = nA by omega,
      show (I + (l : ℤ) - (u.1 + u.2)).toNat = nA + l by omega]
    exact ⟨D, y, hD, h1, h2, h3⟩

end LPPDifferentiability

end
