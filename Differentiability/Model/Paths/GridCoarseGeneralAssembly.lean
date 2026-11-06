/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.GridCoarseGeneralMerge
import Mathlib.Tactic

/-! # Assembly of the four pieces of the coarse scale

* `coarse_direction_facts`: with `θ₁ = min(a, 1 − a)/5` and `c_* = 50 / min(a, 1 − a)`,
  `0 < θ₁ ≤ 1/10`, `5θ₁ ≤ a`, `5θ₁ ≤ 1 − a`, `θ₁ c_* = 10` and `c_* ≥ 100` (Section 5.1 and
  Section B.3 of the differentiability preprint).
* `coarse_pow_bound`: `j² 2^{k−j} ≤ 2 · 2^k` for `j ≤ k` (equation (5.9) of
  the differentiability preprint).
* `coarse_four_piece_path`: for any segment `g` of `γ^u` over a coarse grid interval
  `[I, I + l]` (up-right steps, levels, transverse coordinate within `W0` of `ρ = r(u)`,
  start not trapped, segment weights of the staircase event), on `E_geo`, the staircase event
  (clauses 3 and 4) and a crossing-and-H witness of the coarse good event at the bin of `ρ`, the
  arrival path, the trimmed crossing, the greedy merge path and the tail of `g` form one
  admissible path from `g 0` to `g l` with both defects at most `C₁ j² w + 2t`
  (equation (B.11)) and every vertex within `C₁ j² w` of `ρ`
  (items (C2)-(C4) and (C6) of Section B.3).
-/

public section

namespace LPPDifferentiability
open GreedyAttachment (vertex deviation)

/-- Constants of the direction: `θ₁ = min(a, 1 − a)/5` and `c_* = 50 / min(a, 1 − a)`. -/
theorem coarse_direction_facts (a cstar θ₁ : ℝ) (hθ₁ : θ₁ = min a (1 - a) / 5) (ha₀ : 0 < a)
    (ha₁ : a < 1) (hcs : cstar = 50 / min a (1 - a)) :
    0 < θ₁ ∧ θ₁ ≤ 1 / 10 ∧ 5 * θ₁ ≤ a ∧ 5 * θ₁ ≤ 1 - a ∧ θ₁ * cstar = 10 ∧ 100 ≤ cstar := by
  have hθ0 : 0 < min a (1 - a) := lt_min ha₀ (by linarith)
  have hθa := min_le_left a (1 - a)
  have hθb := min_le_right a (1 - a)
  subst hθ₁ hcs
  refine ⟨div_pos hθ0 (by norm_num), by linarith, by linarith, by linarith, ?_, ?_⟩
  · rw [div_mul_div_comm, div_eq_iff (mul_pos (by norm_num) hθ0).ne']
    ring
  · rw [le_div_iff₀ hθ0]
    linarith

/-- `j² 2^{k−j} ≤ 2 · 2^k` for `j ≤ k`. -/
theorem coarse_pow_bound (j k : ℕ) (hjk : j ≤ k) :
    (j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ) ≤ 2 * 2 ^ k := by
  have hn : j ^ 2 * 2 ^ (k - j) ≤ 2 ^ (k + 1) :=
    calc j ^ 2 * 2 ^ (k - j) ≤ 2 ^ (j + 1) * 2 ^ (k - j) :=
          Nat.mul_le_mul_right _ (sq_le_two_pow_succ j)
      _ = 2 ^ (k + 1) := by rw [← pow_add]; congr 1; omega
  have h : ((j ^ 2 * 2 ^ (k - j) : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hn
  rw [Nat.cast_mul, Nat.cast_pow j 2] at h
  calc (j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := h
    _ = 2 * 2 ^ k := by rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ]; ring

/-- **The four pieces of item (C4) joined, with the cost of item (C6).** -/
theorem coarse_four_piece_path (ω : Environment) (T θ₁ : ℝ) (m1 K1 : ℕ) (Q : Set Lattice)
    (a t G0 dl dr K Cm cstar C₁ Nl ρ : ℝ) (k j w l m' : ℕ) (I : ℤ) :
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
  θ₁ = min a (1 - a) / 5 → 0 < a → a < 1 → 1 ≤ m1 → 1 ≤ K1 → 1 ≤ j → j ≤ k →
  0 ≤ t → cstar = 50 / min a (1 - a) → |dl| ≤ K → |dr| ≤ K → 0 ≤ Cm → 0 ≤ G0 + 2 * Cm →
  8 * cstar * (G0 + 2 * Cm) + 2 * K + 2 * (r0 : ℝ) + 3 * cstar + 1 ≤ C₁ →
  w = 2 ^ (k - j) → m' = ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊ →
  8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)) ≤ (l : ℝ) →
  4 * ((W0 : ℝ) + (r0 : ℝ) + (L : ℝ)) ≤ (w : ℝ) →
  2 * (W0 : ℝ) * K + 4 * (r0 : ℝ) * Cm ≤ (w : ℝ) →
  Nl = 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k →
  Egeo ω T Q →
  (∀ z v : Lattice, z.1 ≤ v.1 → z.2 ≤ v.2 →
    let n : ℕ := (v.1 - z.1 + (v.2 - z.2)).toNat
    let q : ℝ := ((v.1 - z.1 : ℤ) : ℝ) / (n : ℝ)
    let x : ℕ → Lattice := GreedyAttachment.vertex z q {y | (reach ω T y).Finite}
    let e : ℕ × ℕ := ((v.1 - (x (n - L)).1).toNat, (v.2 - (x (n - L)).2).toNat)
    L ≤ n → (n : ℝ) ≤ Nl → (x (n - L)).1 ≤ v.1 → (x (n - L)).2 ≤ v.2 →
    (∀ s, s ≤ n - L → x s ∈ Q) →
    (∀ i : Fin (e.1 + e.2 + 1), (horizontalFirst (x (n - L)) e).vertex i ∈ Q) →
    (∀ s, s < n - L → -T ≤ ω (x s)) →
    (∀ i : Fin (e.1 + e.2 + 1), i.val < e.1 + e.2 →
      -T ≤ ω ((horizontalFirst (x (n - L)) e).vertex i)) →
    -2 * Cm * (n : ℝ) - t / 2 ≤
      (∑ s ∈ Finset.range (n - L), ω (x s)) +
        pathWeight ω (horizontalFirst (x (n - L)) e)) →
  (∀ (z u : Lattice) (Λ : ℤ) (n : ℕ), z.1 + z.2 < Λ →
    ((Λ - (z.1 + z.2) : ℤ) : ℝ) ≤ Nl → (n : ℝ) ≤ Nl → u ∈ Q →
    let q : ℝ := ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) - 2 * (W0 : ℝ) - 3 +
      a * (Λ : ℝ) - (z.1 : ℝ)) / ((Λ - (z.1 + z.2) : ℤ) : ℝ)
    (∀ s, s ≤ n → GreedyAttachment.vertex z q {y | (reach ω T y).Finite} s ∈ Q) →
    (∀ s, s < n → -T ≤ ω (GreedyAttachment.vertex z q {y | (reach ω T y).Finite} s)) →
    -2 * Cm * (n : ℝ) - t / 2 ≤
      ∑ s ∈ Finset.range n, ω (GreedyAttachment.vertex z q {y | (reach ω T y).Finite} s)) →
  ∀ u : Lattice, u ∈ Q → (1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) = ρ →
  (∀ y : Lattice, I ≤ y.1 + y.2 → y.1 + y.2 ≤ I + (l : ℤ) →
    |(1 - a) * (y.1 : ℝ) - a * (y.2 : ℝ) - ρ| ≤ cstar * ((j : ℝ) ^ 2 * (w : ℝ)) → y ∈ Q) →
  ∀ h : ℤ, (h : ℝ) * (w : ℝ) ≤ ρ → ρ < ((h : ℝ) + 1) * (w : ℝ) →
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
  ∀ g : ℕ → Lattice,
    (∀ s < l, g (s + 1) = g s + (1, 0) ∨ g (s + 1) = g s + (0, 1)) →
    (∀ s ≤ l, (g s).1 + (g s).2 = I + (s : ℤ)) →
    (∀ s ≤ l, |(1 - a) * ((g s).1 : ℝ) - a * ((g s).2 : ℝ) - ρ| ≤ (W0 : ℝ)) →
    ¬ (reach ω T (g 0)).Finite →
    (∀ i n, i + n ≤ l → (n : ℝ) ≤ Nl →
      -2 * Cm * (n : ℝ) - t / 2 ≤ ∑ s ∈ Finset.range n, ω (g (i + s))) →
    ∃ (D : ℕ × ℕ) (y : Path (g 0) D), g 0 + ((D.1 : ℤ), (D.2 : ℤ)) = g l ∧
      G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
        pathWeight ω y ≤ C₁ * ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
      G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
        pathWeight ω y ≤ C₁ * ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
      ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) - ρ| ≤
        C₁ * ((j : ℝ) ^ 2 * (w : ℝ)) := by
  intro reach reachBack Ntr W0 L r0 D1 d0 c0 collar Egeo hθ₁ ha₀ ha₁ hm1 hK1 hj1N hjk ht hcs
    hdl hdr hCm hGC hC₁ hw hm'eq hlR hW4 hWK hNleq hE hE3 hE4 u huQ hρu hQ h hh1 hh2 N hN1 hN2 c
    hc x₀ d x hx0 hd hxc hxW hH g hgs hgl hgr hgt hgw
  obtain ⟨hθpos, hθle, h5a, h5b, hcθ, hc100⟩ := coarse_direction_facts a cstar θ₁ hθ₁ ha₀ ha₁ hcs
  set P : ℝ := (j : ℝ) ^ 2 * (w : ℝ) with hP
  have hW01 : (1 : ℝ) ≤ W0 := by exact_mod_cast (show 1 ≤ Ntr + 1 by omega)
  have hr0 : (0 : ℝ) ≤ r0 := Nat.cast_nonneg r0
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj1N
  have hj2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := one_le_pow₀ hj1
  have hPw : (w : ℝ) ≤ P := le_mul_of_one_le_left (Nat.cast_nonneg w) hj2
  have hP0 : 0 ≤ P := mul_nonneg (by positivity) (Nat.cast_nonneg w)
  have hr01 : (1 : ℝ) ≤ r0 := by
    have := Nat.mul_le_mul hK1 (show 1 ≤ 2 * L + 1 by omega)
    exact_mod_cast (show 1 ≤ K1 * (2 * L + 1) + Ntr by omega)
  have hwbig : 4 * (W0 : ℝ) + 4 ≤ w := by linarith only [hW4, hr01, hL0]
  have hK0 : 0 ≤ K := (abs_nonneg dl).trans hdl
  have hm'1 : cstar * P ≤ m' := by rw [hm'eq]; exact Nat.le_ceil _
  have hm'2 : (m' : ℝ) < cstar * P + 1 := by
    rw [hm'eq]
    exact Nat.ceil_lt_add_one (mul_nonneg (by linarith only [hc100]) hP0)
  have hcP : 100 * P ≤ cstar * P := mul_le_mul_of_nonneg_right hc100 hP0
  have hml : 2 * m' + 2 * r0 + 2 ≤ l := by
    have : ((2 * m' + 2 * r0 + 2 : ℕ) : ℝ) ≤ (l : ℝ) := by
      push_cast; linarith only [hm'2, hlR, hW4, hwbig, hPw, hcP, hr0, hL0, hW01, hP0]
    exact_mod_cast this
  have hLm : L ≤ m' := by
    have : (L : ℝ) ≤ m' := by linarith only [hW4, hW01, hr0, hPw, hcP, hm'1, hP0]
    exact_mod_cast this
  have hm'pos : 1 ≤ m' := by
    have : (1 : ℝ) ≤ m' := by linarith only [hm'1, hcP, hPw, hwbig, hW01, hP0]
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hw2k : (w : ℝ) ≤ 2 ^ k := by
    rw [hw]
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) (Nat.sub_le k j)
  have hNl : (m' : ℝ) + r0 ≤ Nl := by
    have hjk' : (j : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg j) (by exact_mod_cast hjk) 2
    have hk0 : (0 : ℝ) ≤ (k : ℝ) ^ 2 * 2 ^ k := by positivity
    have hPk2 : P ≤ (k : ℝ) ^ 2 * 2 ^ k := mul_le_mul hjk' hw2k (Nat.cast_nonneg w) (by positivity)
    have hX := mul_le_mul_of_nonneg_left hPk2 (by linarith only [hc100] : (0 : ℝ) ≤ cstar)
    have hY : (2 : ℝ) ^ k ≤ (k : ℝ) ^ 2 * 2 ^ k :=
      le_mul_of_one_le_left (by positivity) (one_le_pow₀ hk1)
    have hZ : (k : ℝ) ^ 2 * 2 ^ k ≤ cstar * ((k : ℝ) ^ 2 * 2 ^ k) :=
      le_mul_of_one_le_left (by positivity) (by linarith only [hc100])
    rw [hNleq]
    linarith only [hm'2, hX, hY, hZ, hk0, hW4, hW01, hL0, hw2k, hcP, hPw, hP0, hwbig]
  have hcG : 0 ≤ cstar * (G0 + 2 * Cm) := mul_nonneg (by linarith only [hc100]) hGC
  have hcC : cstar ≤ C₁ := by linarith only [hC₁, hcG, hK0, hr0, hc100]
  -- The crossing: levels, weights, location.
  obtain ⟨yx, hyx0, hyxv, hyxs, -⟩ := exists_seq_of_path x
  have hxlev : ∀ i : Fin (d.1 + d.2 + 1),
      (x.vertex i).1 + (x.vertex i).2 = I + m' + (i.val : ℤ) := fun i => by
    have h1 := (seq_coords yx _ hyxs i.val (by have := i.isLt; omega)).2.2
    rw [hyx0] at h1
    rw [hyxv]
    omega
  have hNw : (N : ℝ) * w ≤ P :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hN2) (Nat.cast_nonneg w)
  have hNw1 : (w : ℝ) ≤ N * w := le_mul_of_one_le_left (Nat.cast_nonneg w) (by exact_mod_cast hN1)
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  have hxρ : ∀ i, |(1 - a) * ((x.vertex i).1 : ℝ) - a * ((x.vertex i).2 : ℝ) - ρ| ≤ 39 * P :=
    fun i => by
      obtain ⟨a1, a2⟩ := abs_le.mp (hxc i)
      exact abs_le.mpr
        ⟨by linarith only [a1, a2, hc1, hc2, hh1, hh2, hNw, hNw1, hPw, hwbig, hW01],
          by linarith only [a1, a2, hc1, hc2, hh1, hh2, hNw, hNw1, hPw, hwbig, hW01]⟩
  have hxw : ∀ i, ω (x.vertex i) ≤ w := fun i =>
    hH _ (by have := hxlev i; omega) (by have := hxlev i; have := i.isLt; omega) (hxc i)
  have hxQ : ∀ i, x.vertex i ∈ Q := fun i => hQ _ ((by have := hxlev i; omega))
    ((by have := hxlev i; have := i.isLt; omega)) ((hxρ i).trans (by linarith only [hcP, hP0]))
  -- Trimming (C2).
  obtain ⟨v, v', α, β, hα, hβ1, hβ2, hvl, hv'l, ⟨iv, hiv⟩, ⟨iv', hiv'⟩, hbox, hv'nt, e2, p2,
      hend2, hw2, hloc2⟩ :=
    coarse_trim_piece ω T θ₁ m1 K1 Q a ρ (cstar * P) w (G0 * ((l - 2 * m' : ℕ) : ℝ) - K * w)
      hθpos hθle hm1 hK1 hE (Nat.cast_nonneg w) x₀ d x (by show 2 * r0 + 1 ≤ d.1 + d.2; omega) hxQ
      hxw (fun i => (hxρ i).trans (by linarith only [hcP, hP0])) hxW.le
  have hα' : α ≤ r0 := hα
  have hβ1' : d.1 + d.2 ≤ β + r0 := hβ1
  have hw2' : G0 * ((l - 2 * m' : ℕ) : ℝ) - K * w - 2 * (r0 : ℝ) * w ≤ pathWeight ω p2 := hw2
  have hvρ : |(1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ) - ρ| ≤ 39 * P := by rw [← hiv]; exact hxρ iv
  have hv'ρ : |(1 - a) * (v'.1 : ℝ) - a * (v'.2 : ℝ) - ρ| ≤ 39 * P := by
    rw [← hiv']; exact hxρ iv'
  have hv'c := hxc iv'
  rw [hiv'] at hv'c
  have hv'Q : v' ∈ Q := by rw [← hiv']; exact hxQ iv'
  have hθm : 40 * P ≤ 4 * θ₁ * (m' : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hm'1 hθpos.le
    have h2 : θ₁ * (cstar * P) = 10 * P := by rw [← mul_assoc, hcθ]
    linarith only [h1, h2]
  have hαR : (α : ℝ) ≤ r0 := by exact_mod_cast hα'
  have hθα : 0 ≤ θ₁ * (α : ℝ) := mul_nonneg hθpos.le (Nat.cast_nonneg α)
  have hg0 := hgl 0 (Nat.zero_le _)
  have hg0ρ := hgr 0 (Nat.zero_le _)
  obtain ⟨g01, g02⟩ := abs_le.mp hg0ρ
  obtain ⟨v1, v2⟩ := abs_le.mp hvρ
  -- Piece 1: the arrival path.
  obtain ⟨d1, p1, hend1, hw1, hloc1⟩ := coarse_arrival_piece ω T θ₁ m1 K1 Q a Cm t Nl ρ
    (40 * P) (cstar * P) hθpos hθle hm1 hK1 hE h5a h5b
    (by
      show 40 * P + (W0 : ℝ) + (L : ℝ) ≤ cstar * P
      linarith only [hcP, hW4, hPw, hW01, hr0, hL0, hP0]) hE3 (g 0) v (m' + α)
    (hQ _ ((by omega)) ((by omega)) (hg0ρ.trans (by linarith only [hwbig, hPw, hcP, hP0]))) hgt hbox
    (by omega) (by show L ≤ m' + α; omega) (by push_cast; linarith only [hNl, hαR])
    (abs_le.mpr ⟨by push_cast; linarith only [v1, v2, g01, g02, hθm, hθα, hwbig, hPw, hW01],
      by push_cast; linarith only [v1, v2, g01, g02, hθm, hθα, hwbig, hPw, hW01]⟩)
    (abs_le.mpr ⟨by linarith only [g01, hwbig, hPw, hP0, hW01],
      by linarith only [g02, hwbig, hPw, hP0, hW01]⟩)
    (abs_le.mpr ⟨by linarith only [v1, hP0], by linarith only [v2, hP0]⟩)
    (fun y h1 h2 h3 => hQ y ((by omega)) ((by omega)) h3)
  -- Pieces 3 and 4: the greedy merge path and the tail of `γ^u`.
  have hβl : m' + β + m' ≤ l := by omega
  have hn3 : l - (m' + β) ≤ m' + r0 := by omega
  have hn3R : ((l - (m' + β) : ℕ) : ℝ) ≤ m' + r0 := by exact_mod_cast hn3
  have hm3R : (m' : ℝ) ≤ ((l - (m' + β) : ℕ) : ℝ) := by
    exact_mod_cast (by omega : m' ≤ l - (m' + β))
  have hθn3 := mul_le_mul_of_nonneg_left hm3R hθpos.le
  have hgβ := hgr (m' + β) (by omega)
  obtain ⟨b1, b2⟩ := abs_le.mp hgβ
  obtain ⟨w1, w2⟩ := abs_le.mp hv'ρ
  obtain ⟨c1, c2⟩ := abs_le.mp hv'c
  obtain ⟨d3, p3, hend3, hw3, hloc3⟩ := coarse_merge_piece ω T θ₁ m1 K1 Q a Cm t Nl ρ
    (40 * P) (cstar * P) hθpos hθle hm1 hK1 hE h5a h5b
    (by show 40 * P + (W0 : ℝ) + 1 ≤ cstar * P; linarith only [hcP, hwbig, hPw, hP0])
    (by show 2 * (W0 : ℝ) + 3 ≤ 40 * P; linarith only [hwbig, hPw, hP0, hW01]) hE4 u v'
    (fun s => g (m' + β + s))
    (l - (m' + β)) huQ hρu hv'Q hv'nt (by omega) (by linarith only [hn3R, hNl])
    (fun s hs => hgs (m' + β + s) (by omega))
    (by show (g (m' + β)).1 + (g (m' + β)).2 = v'.1 + v'.2; have := hgl (m' + β) (by omega); omega)
    (fun s hs => hgr (m' + β + s) (by omega))
    (fun i hi => (hgw (m' + β + i) (l - (m' + β) - i) (by omega) (by
        have : ((l - (m' + β) - i : ℕ) : ℝ) ≤ ((l - (m' + β) : ℕ) : ℝ) := by
          exact_mod_cast Nat.sub_le _ _
        linarith only [this, hn3R, hNl])).trans_eq
      (Finset.sum_congr rfl fun s _ => by
        show ω (g (m' + β + i + s)) = ω (g (m' + β + (i + s)))
        rw [Nat.add_assoc (m' + β) i s]))
    (by
      show (1 - a) * ((g (m' + β)).1 : ℝ) - a * ((g (m' + β)).2 : ℝ) <
        (1 - a) * (v'.1 : ℝ) - a * (v'.2 : ℝ)
      linarith only [b2, c1, hc1, hh2, hNw1, hwbig, hW01])
    (abs_le.mpr ⟨by linarith only [w1, w2, hθm, hθn3, hwbig, hPw, hW01, hP0],
      by linarith only [w1, w2, hθm, hθn3, hwbig, hPw, hW01, hP0]⟩)
    (abs_le.mpr ⟨by linarith only [w1, hP0], by linarith only [w2, hP0]⟩)
    (fun y h1 h2 h3 => hQ y ((by omega)) ((by omega)) h3)
  have hend3' : v' + ((d3.1 : ℤ), (d3.2 : ℤ)) = g l := by
    rw [show l = m' + β + (l - (m' + β)) by omega]
    exact hend3
  -- Joining the four pieces.
  obtain ⟨D12, p12, hD12, hw12, hloc12⟩ := exists_path_join ω
    (fun y => (1 - a) * (y.1 : ℝ) - a * (y.2 : ℝ) - ρ) (cstar * P) _ _ (g 0) v v'
    ⟨d1, p1, hend1, hw1, hloc1⟩ ⟨e2, p2, hend2, hw2', hloc2⟩
  obtain ⟨D, y, hD, hyw, hyloc⟩ := exists_path_join ω
    (fun y => (1 - a) * (y.1 : ℝ) - a * (y.2 : ℝ) - ρ) (cstar * P) _ _ (g 0) v' (g l)
    ⟨D12, p12, hD12, hw12, hloc12⟩ ⟨d3, p3, hend3', hw3, hloc3⟩
  -- Cost (equation (B.11)) and location.
  have e1 : (g 0).1 + (D.1 : ℤ) = (g l).1 := congrArg Prod.fst hD
  have e2 : (g 0).2 + (D.2 : ℤ) = (g l).2 := congrArg Prod.snd hD
  have hgl' := hgl l le_rfl
  have hDl : (D.1 : ℝ) + D.2 = l := by exact_mod_cast (by omega : (D.1 : ℤ) + D.2 = l)
  have e1R : ((g 0).1 : ℝ) + D.1 = (g l).1 := by exact_mod_cast e1
  have e2R : ((g 0).2 : ℝ) + D.2 = (g l).2 := by exact_mod_cast e2
  obtain ⟨gl1, gl2⟩ := abs_le.mp (hgr l le_rfl)
  have hrDeq : (1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ) = ((1 - a) * ((g l).1 : ℝ) -
      a * ((g l).2 : ℝ)) - ((1 - a) * ((g 0).1 : ℝ) - a * ((g 0).2 : ℝ)) := by
    linear_combination (1 - a) * e1R - a * e2R
  have hrD : |(1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)| ≤ 2 * W0 := by
    rw [hrDeq, abs_le]
    constructor <;> linarith only [g01, g02, gl1, gl2]
  have hσ : ∀ σ : ℝ, |σ| ≤ K → σ * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) ≤ 2 * W0 * K :=
    fun σ hs => (le_abs_self _).trans ((abs_mul _ _).le.trans
      ((mul_le_mul hs hrD (abs_nonneg _) hK0).trans (le_of_eq (by ring))))
  have hG0l : G0 * ((D.1 : ℝ) + D.2) = G0 * l := by rw [hDl]
  have hc2m : ((l - 2 * m' : ℕ) : ℝ) = l - 2 * m' := by
    rw [eq_sub_iff_add_eq]
    exact_mod_cast Nat.sub_add_cancel (show 2 * m' ≤ l by omega)
  have hc3 : ((l - (m' + β) : ℕ) : ℝ) = l - m' - β := by
    rw [sub_sub, eq_sub_iff_add_eq]
    exact_mod_cast Nat.sub_add_cancel (show m' + β ≤ l by omega)
  have hβR : (l : ℝ) - 2 * m' ≤ β + r0 := by
    rw [← hc2m]
    exact_mod_cast (by omega : l - 2 * m' ≤ β + r0)
  rw [hc2m, hc3] at hyw
  push_cast at hyw
  have hCmb := mul_le_mul_of_nonneg_left
    (show ((m' : ℝ) + α) + (l - m' - β) ≤ 2 * m' + 2 * r0 by linarith only [hβR, hαR])
    (by linarith only [hCm] : 0 ≤ 2 * Cm)
  have hG2 := mul_le_mul_of_nonneg_right (show 2 * (m' : ℝ) ≤ 4 * cstar * P by
    linarith only [hm'2, hcP, hPw, hwbig, hW01, hP0]) hGC
  have hKw := mul_le_mul_of_nonneg_left hPw (by linarith only [hK0, hr0] : 0 ≤ K + 2 * (r0 : ℝ))
  have hC1P := mul_le_mul_of_nonneg_right
    (show 4 * cstar * (G0 + 2 * Cm) + K + 2 * (r0 : ℝ) + 1 ≤ C₁ by
      linarith only [hC₁, hcG, hK0, hc100]) hP0
  refine ⟨D, y, hD, ?_, ?_, fun i => (hyloc i).trans (mul_le_mul_of_nonneg_right hcC hP0)⟩
  · have := hσ dl hdl
    linarith only [this, hyw, hG0l, hCmb, hG2, hKw, hC1P, hWK, hPw, ht]
  · have := hσ dr hdr
    linarith only [this, hyw, hG0l, hCmb, hG2, hKw, hC1P, hWK, hPw, ht]

end LPPDifferentiability

end
