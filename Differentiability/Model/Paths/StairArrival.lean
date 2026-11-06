/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.StairGreedyForward
public import LPP_Foundations.Model.Paths.HorizontalFirst
import Mathlib.Tactic

/-! # The arrival path (item (iii) of Lemma B.5)

The items (i) to (v) cited here are those of Lemma B.5 of the differentiability preprint.

From a vertex `z` that is not trapped, run the greedy path of item (ii) along the segment to `v`
until the remaining displacement has level `L`, then take all remaining `e₁` steps followed by all
remaining `e₂` steps (`horizontalFirst`). The deviation bound `W0` of item (ii) is proved by an
induction on the level: the region membership of a greedy vertex comes from the margin
hypothesis and the deviation bound at the *same* level, which the core of item (ii) provides
from the region membership of the earlier vertices only. The box hypothesis keeps the last phase
clear of very bad vertices, and the box has width `L`, which gives the final deviation bound. -/

public section

namespace LPPDifferentiability
open GreedyAttachment (vertex deviation)

private abbrev reachSet (ω : Environment) (T : ℝ) (z : Lattice) : Set Lattice :=
  {y | ∃ (d : ℕ × ℕ) (q : Path z d), z + ((d.1 : ℤ), (d.2 : ℤ)) = y ∧
    ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}

private theorem reach_of_vertex (ω : Environment) (T : ℝ) {y w : Lattice} {d : ℕ × ℕ}
    (q : Path y d) (hw : y + ((d.1 : ℤ), (d.2 : ℤ)) = w)
    (hq : ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i))
    (k : Fin (d.1 + d.2 + 1)) : w ∈ reachSet ω T (q.vertex k) := by
  have hle := q.splitDisplacement_le k
  have h1 := q.splitDisplacement_fst_cast k
  have h2 := q.splitDisplacement_snd_cast k
  refine ⟨d - q.splitDisplacement k, q.suffix k, ?_, fun i hi => ?_⟩
  · rw [← hw]
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Nat.cast_sub hle.1, Nat.cast_sub hle.2] <;> omega
  · have hl := q.suffix_length k
    have hk2 := k.isLt
    exact hq ⟨k.val + i.val, by show k.val + i.val < _; omega⟩ (by show k.val + i.val < _; omega)

private theorem reach_finite_of_succ (ω : Environment) (T : ℝ) (y : Lattice)
    (h1 : (reachSet ω T (y + (1, 0))).Finite) (h2 : (reachSet ω T (y + (0, 1))).Finite) :
    (reachSet ω T y).Finite := by
  refine (((Set.finite_singleton y).union h1).union h2).subset ?_
  rintro w ⟨d, q, hw, hq⟩
  by_cases hd : d.1 + d.2 = 0
  · rw [show d.1 = 0 by omega, show d.2 = 0 by omega] at hw
    exact Or.inl (Or.inl (show w = y by rw [← hw]; apply Prod.ext <;> simp))
  · have hpos : 0 < d.1 + d.2 := Nat.pos_of_ne_zero hd
    have hs := q.step ⟨0, hpos⟩
    rw [show ((⟨0, hpos⟩ : Fin (d.1 + d.2)).castSucc : Fin (d.1 + d.2 + 1)) = 0 from Fin.ext rfl,
      q.start, show (⟨0, hpos⟩ : Fin (d.1 + d.2)).succ = (⟨1, by omega⟩ : Fin (d.1 + d.2 + 1))
        from Fin.ext rfl] at hs
    have hmem := reach_of_vertex ω T q hw hq ⟨1, by omega⟩
    rcases hs with h | h <;> rw [h] at hmem
    · exact Or.inl (Or.inr hmem)
    · exact Or.inr hmem

private theorem reach_finite_of_bad (ω : Environment) (T : ℝ) (x : Lattice) (h : ω x < -T) :
    (reachSet ω T x).Finite := by
  refine (Set.finite_singleton x).subset ?_
  rintro w ⟨d, q, hw, hq⟩
  by_cases hd : d.1 + d.2 = 0
  · rw [show d.1 = 0 by omega, show d.2 = 0 by omega] at hw
    exact show w = x by rw [← hw]; apply Prod.ext <;> simp
  · have h0 := hq ⟨0, by omega⟩ (by show 0 < d.1 + d.2; omega)
    rw [show (⟨0, by omega⟩ : Fin (d.1 + d.2 + 1)) = 0 from Fin.ext rfl, q.start] at h0
    exact absurd h0 (not_le.mpr h)

/-- Room left after `L` more levels: both remaining coordinates are positive. -/
private theorem arrive_room (θ q : ℝ) (L W : ℕ) (hq1 : θ ≤ q) (hq2 : q ≤ 1 - θ)
    (hLθ : 4 * ((W : ℝ) + 2) ≤ (L : ℝ) * θ) (d : ℝ) (hd : |d| ≤ (W : ℝ)) :
    3 * (W : ℝ) + 8 ≤ (L : ℝ) * q - d ∧ 3 * (W : ℝ) + 8 ≤ (L : ℝ) * (1 - q) + d := by
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have h1 := mul_le_mul_of_nonneg_left hq1 hL0
  have h2 := mul_le_mul_of_nonneg_left (show θ ≤ 1 - q by linarith) hL0
  obtain ⟨hd1, hd2⟩ := abs_le.mp hd
  constructor <;> nlinarith [h1, h2, hd1, hd2]

/-- Remaining displacement of a level-`N` vertex `p`, `L` levels before the end of the segment. -/
private theorem arrive_remaining (z v p : Lattice) (n N L : ℕ) (q : ℝ)
    (hn : (n : ℤ) = (v.1 - z.1) + (v.2 - z.2)) (hn0 : n ≠ 0)
    (hq : q = ((v.1 - z.1 : ℤ) : ℝ) / (n : ℝ)) (hNL : N + L = n)
    (hlev : p.1 + p.2 = z.1 + z.2 + (N : ℤ)) :
    ((v.1 - p.1 : ℤ) : ℝ) = (L : ℝ) * q - deviation z q N p ∧
      ((v.2 - p.2 : ℤ) : ℝ) = (L : ℝ) * (1 - q) + deviation z q N p := by
  have hn0' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hnq : (n : ℝ) * q = ((v.1 - z.1 : ℤ) : ℝ) := by
    have h := (eq_div_iff hn0').mp hq
    linarith [h]
  have hnR : (n : ℝ) = (v.1 : ℝ) + (v.2 : ℝ) - z.1 - z.2 := by
    exact_mod_cast (by omega : (n : ℤ) = v.1 + v.2 - z.1 - z.2)
  have hNR : (N : ℝ) + (L : ℝ) = (n : ℝ) := by exact_mod_cast hNL
  have hlevR : (p.1 : ℝ) + (p.2 : ℝ) = (z.1 : ℝ) + (z.2 : ℝ) + (N : ℝ) := by exact_mod_cast hlev
  have hLq : (L : ℝ) * q = (n : ℝ) * q - (N : ℝ) * q := by rw [← hNR]; ring
  push_cast at hnq
  unfold GreedyAttachment.deviation
  push_cast
  constructor <;> linarith [hnq, hLq, hnR, hNR, hlevR]

/-- The vertices of the final `horizontalFirst` phase lie in the box `v - [0, L]²`. -/
private theorem arrive_hf_box (p v : Lattice) (L : ℕ) (e : ℕ × ℕ) (he1 : (e.1 : ℤ) = v.1 - p.1)
    (he2 : (e.2 : ℤ) = v.2 - p.2) (hL : e.1 + e.2 = L) (j : Fin (e.1 + e.2 + 1))
    (hj : j.val < e.1 + e.2) :
    v.1 - (L : ℤ) ≤ ((horizontalFirst p e).vertex j).1 ∧ ((horizontalFirst p e).vertex j).1 ≤ v.1 ∧
      v.2 - (L : ℤ) ≤ ((horizontalFirst p e).vertex j).2 ∧
      ((horizontalFirst p e).vertex j).2 ≤ v.2 := by
  have hx : ((horizontalFirst p e).vertex j).1 = p.1 + ((min j.val e.1 : ℕ) : ℤ) := rfl
  have hy : ((horizontalFirst p e).vertex j).2 = p.2 + ((j.val - e.1 : ℕ) : ℤ) := rfl
  rw [hx, hy]
  rcases le_total j.val e.1 with h | h
  · rw [Nat.min_eq_left h]
    omega
  · rw [Nat.min_eq_right h]
    omega

/-- The vertices of the final phase stay within `W + L` of the line. -/
private theorem arrive_hf_dev (z p : Lattice) (q : ℝ) (N L : ℕ) (e : ℕ × ℕ) (W : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hdev : |deviation z q N p| ≤ W) (hL : e.1 + e.2 = L)
    (j : Fin (e.1 + e.2 + 1)) :
    |deviation z q (N + j.val) ((horizontalFirst p e).vertex j)| ≤ W + (L : ℝ) := by
  have hj : j.val ≤ L := by have := j.isLt; omega
  have hx : ((horizontalFirst p e).vertex j).1 = p.1 + ((min j.val e.1 : ℕ) : ℤ) := rfl
  have heq : deviation z q (N + j.val) ((horizontalFirst p e).vertex j) =
      deviation z q N p + (((min j.val e.1 : ℕ) : ℝ) - (j.val : ℝ) * q) := by
    unfold GreedyAttachment.deviation
    rw [hx]
    push_cast
    ring
  have hm0 : (0 : ℝ) ≤ ((min j.val e.1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmj : ((min j.val e.1 : ℕ) : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast Nat.min_le_left _ _
  have hjL : (j.val : ℝ) ≤ (L : ℝ) := by exact_mod_cast hj
  have hjq0 : 0 ≤ (j.val : ℝ) * q := mul_nonneg (Nat.cast_nonneg _) hq0
  have hjq1 : (j.val : ℝ) * q ≤ (j.val : ℝ) :=
    mul_le_of_le_one_right (Nat.cast_nonneg _) hq1
  obtain ⟨hd1, hd2⟩ := abs_le.mp hdev
  rw [heq, abs_le]
  constructor <;> linarith

/-- **Item (iii) of Lemma B.5, the arrival path.** -/
theorem stair_greedy_arrival (ω : Environment) (T θ₁ : ℝ) (m1 K1 : ℕ) (Q : Set Lattice) :
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
  let boxFree : Environment → ℝ → Lattice → Prop := fun ω T v =>
    ∀ y : Lattice, v.1 - (L : ℤ) ≤ y.1 → y.1 ≤ v.1 → v.2 - (L : ℤ) ≤ y.2 → y.2 ≤ v.2 →
      -T ≤ ω y
  0 < θ₁ → θ₁ ≤ 1 / 10 → 1 ≤ m1 → 1 ≤ K1 → Egeo ω T Q →
  ∀ z v : Lattice, z ∈ Q → ¬ (reach ω T z).Finite → z.1 ≤ v.1 → z.2 ≤ v.2 →
    let n : ℕ := (v.1 - z.1 + (v.2 - z.2)).toNat
    let q : ℝ := ((v.1 - z.1 : ℤ) : ℝ) / (n : ℝ)
    let x : ℕ → Lattice := GreedyAttachment.vertex z q {y | (reach ω T y).Finite}
    L ≤ n → θ₁ ≤ q → q ≤ 1 - θ₁ → boxFree ω T v →
    (∀ y : Lattice, z.1 + z.2 ≤ y.1 + y.2 → y.1 + y.2 ≤ v.1 + v.2 →
      |GreedyAttachment.deviation z q (y.1 + y.2 - (z.1 + z.2)).toNat y| ≤ (W0 : ℝ) →
        y ∈ Q) →
    let e : ℕ × ℕ := ((v.1 - (x (n - L)).1).toNat, (v.2 - (x (n - L)).2).toNat)
    (x (n - L)).1 ≤ v.1 ∧ (x (n - L)).2 ≤ v.2 ∧ e.1 + e.2 = L ∧
    (∀ t, t ≤ n - L → x t ∈ Q ∧ |GreedyAttachment.deviation z q t (x t)| ≤ (W0 : ℝ)) ∧
    (∀ t, t < n - L → -T ≤ ω (x t)) ∧
    (∀ i : Fin (e.1 + e.2 + 1), i.val < e.1 + e.2 →
      -T ≤ ω ((horizontalFirst (x (n - L)) e).vertex i)) ∧
    (∀ i : Fin (e.1 + e.2 + 1),
      |GreedyAttachment.deviation z q (n - L + i.val)
        ((horizontalFirst (x (n - L)) e).vertex i)| ≤ (W0 : ℝ) + (L : ℝ)) := by
  intro reach reachBack Ntr W0 L r0 D1 d0 c0 collar Egeo boxFree hθ hθ' hm hK hE z v _ hz hz1 hz2
    n q x hLn hq1 hq2 hbox hmargin e
  have hNtr : 1 ≤ Ntr := Nat.mul_pos hK (by positivity)
  have hc0 : 1 ≤ c0 := by show 1 ≤ W0 + 2 * L + 1; omega
  have hD1 : ⌊2 * ((Ntr + 1 : ℕ) : ℝ) / θ₁⌋₊ + 4 * (Ntr + 1) + 8 ≤ D1 := by
    show _ ≤ ⌊2 * ((Ntr + 1 : ℕ) : ℝ) / θ₁⌋₊ + 4 * (Ntr + 1) + 2 * r0 + 2 * L + 8
    omega
  have hPC : ∀ y ∈ Q, y + (1, 0) ∈ collar Q c0 ∧ y + (0, 1) ∈ collar Q c0 := fun y hy =>
    ⟨⟨y, hy, by rw [l1_one y _ (Or.inl rfl)]; exact_mod_cast hc0⟩,
      ⟨y, hy, by rw [l1_one y _ (Or.inr rfl)]; exact_mod_cast hc0⟩⟩
  have hcand : ∀ y : Lattice, y ∉ {y | (reach ω T y).Finite} →
      y + (1, 0) ∉ {y | (reach ω T y).Finite} ∨ y + (0, 1) ∉ {y | (reach ω T y).Finite} := by
    intro y hy
    by_contra hcon
    have hcon' := not_or.mp hcon
    exact hy (reach_finite_of_succ ω T y (not_not.mp hcon'.1) (not_not.mp hcon'.2))
  have hchain := (stair_trapped_components_le ω T θ₁ m1 K1 Q hθ hθ' hm hK hE).1
  have hLpos : 0 < L := by
    show 0 < ⌈4 * ((W0 : ℝ) + 2) / θ₁⌉₊
    exact Nat.ceil_pos.mpr (by positivity)
  have hLθ : 4 * ((W0 : ℝ) + 2) ≤ (L : ℝ) * θ₁ := by
    have h := Nat.le_ceil (4 * ((W0 : ℝ) + 2) / θ₁)
    rw [div_le_iff₀ hθ] at h
    exact h
  have hn0 : n ≠ 0 := by omega
  have hnZ : (n : ℤ) = (v.1 - z.1) + (v.2 - z.2) := by
    show (((v.1 - z.1 + (v.2 - z.2)).toNat : ℕ) : ℤ) = _
    omega
  have hq0 : 0 ≤ q := by linarith
  have hq1' : q ≤ 1 := by linarith
  have hQx : ∀ t, t ≤ n - L → x t ∈ Q := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      have h := (stair_greedy_core θ₁ q Ntr D1 {y | (reach ω T y).Finite} Q (collar Q c0) z hθ
        hq1 hq2 hNtr hD1 hPC hcand hchain hz t (fun i hi => ih i hi (by omega)) t le_rfl).2
      have hxl : (x t).1 + (x t).2 = z.1 + z.2 + (t : ℤ) :=
        GreedyAttachment.level z q {y | (reach ω T y).Finite} t
      have hlev' : ((x t).1 + (x t).2 - (z.1 + z.2)).toNat = t := by omega
      refine hmargin (x t) (by omega) (by omega) ?_
      rw [hlev']
      exact h
  have hcoreAt : ∀ t, t ≤ n - L → x t ∉ {y | (reach ω T y).Finite} ∧
      |deviation z q t (x t)| ≤ (W0 : ℝ) := fun t ht =>
    stair_greedy_core θ₁ q Ntr D1 {y | (reach ω T y).Finite} Q (collar Q c0) z hθ hq1 hq2 hNtr
      hD1 hPC hcand hchain hz t (fun i hi => hQx i (by omega)) t le_rfl
  have hbad : ∀ t, t ≤ n - L → -T ≤ ω (x t) := by
    intro t ht
    by_contra h
    exact (hcoreAt t ht).1 (reach_finite_of_bad ω T _ (not_le.mp h))
  have hlevN : (x (n - L)).1 + (x (n - L)).2 = z.1 + z.2 + ((n - L : ℕ) : ℤ) :=
    GreedyAttachment.level z q {y | (reach ω T y).Finite} (n - L)
  have hrem := arrive_remaining z v (x (n - L)) n (n - L) L q hnZ hn0 rfl (by omega) hlevN
  have hroom := arrive_room θ₁ q L W0 hq1 hq2 hLθ _ (hcoreAt (n - L) le_rfl).2
  have hW0 : (0 : ℝ) ≤ (W0 : ℝ) := Nat.cast_nonneg W0
  have hA : (0 : ℤ) ≤ v.1 - (x (n - L)).1 := by
    have h : (0 : ℝ) ≤ ((v.1 - (x (n - L)).1 : ℤ) : ℝ) := by
      rw [hrem.1]; linarith [hroom.1]
    exact_mod_cast h
  have hB : (0 : ℤ) ≤ v.2 - (x (n - L)).2 := by
    have h : (0 : ℝ) ≤ ((v.2 - (x (n - L)).2 : ℤ) : ℝ) := by
      rw [hrem.2]; linarith [hroom.2]
    exact_mod_cast h
  have he1 : (e.1 : ℤ) = v.1 - (x (n - L)).1 := by
    show (((v.1 - (x (n - L)).1).toNat : ℕ) : ℤ) = _
    omega
  have he2 : (e.2 : ℤ) = v.2 - (x (n - L)).2 := by
    show (((v.2 - (x (n - L)).2).toNat : ℕ) : ℤ) = _
    omega
  have hL : e.1 + e.2 = L := by omega
  refine ⟨by omega, by omega, hL, fun t ht => ⟨hQx t ht, (hcoreAt t ht).2⟩,
    fun t ht => hbad t ht.le, fun i hi => ?_, fun i =>
    arrive_hf_dev z (x (n - L)) q (n - L) L e (W0 : ℝ) hq0 hq1' (hcoreAt (n - L) le_rfl).2 hL i⟩
  obtain ⟨h1, h2, h3, h4⟩ := arrive_hf_box (x (n - L)) v L e he1 he2 hL i hi
  exact hbox _ h1 h2 h3 h4

end LPPDifferentiability
