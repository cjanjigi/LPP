/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.GridCoarseGeneralPieces
public import Differentiability.Model.Paths.StairArrival
public import Differentiability.Model.StairTrim
import Mathlib.Tactic

/-! # The arrival piece and the trimmed crossing of the coarse scale

Two of the four pieces of item (C4) of Section B.3 of the differentiability preprint:

* `coarse_arrival_piece`: the path of Lemma B.5 (iii) from a vertex `z` that is not
  trapped to a vertex `v` with a very-bad-free box, as one `Path`, with the weight bound of the
  staircase event (clause 3) and every vertex within `B` of `ρ` in transverse coordinate. The
  slope condition is derived from `|r(v) − r(z)| ≤ 4 θ₁ n`, and the region membership of every
  vertex (also of the final `horizontalFirst` phase) from the margin hypothesis.
* `coarse_trim_piece`: the trimming of item (C2):
  a crossing is cut at a vertex with a very-bad-free box
  among its first `r0 + 1` vertices and at a vertex that is not trapped among its last `r0 + 1`;
  every removed collected vertex has weight at most `w`, so the cut path loses at most `2 r0 w`.
* `line_transverse_le`: a point within deviation `Dv` of the line from `z` toward a target whose
  transverse coordinate, like that of `z`, is within `B0` of `ρ` is within `B0 + Dv` of `ρ`.
-/

public section

namespace LPPDifferentiability
open GreedyAttachment (vertex deviation)

/-- A point near the line from `z` to a target is near `ρ` when both ends are. -/
theorem line_transverse_le (a q ρ B0 Dv rT : ℝ) (z y : Lattice) (t N : ℕ) (hN : 0 < N)
    (htN : t ≤ N) (hq : (q - a) * (N : ℝ) = rT - ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)))
    (hz : |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - ρ| ≤ B0) (hT : |rT - ρ| ≤ B0)
    (hlev : y.1 + y.2 = z.1 + z.2 + (t : ℤ)) (hdev : |deviation z q t y| ≤ Dv) :
    |(1 - a) * (y.1 : ℝ) - a * (y.2 : ℝ) - ρ| ≤ B0 + Dv := by
  have he := GreedyAttachment.transverse_deviation_eq z y q a t hlev
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have htR : (t : ℝ) ≤ N := by exact_mod_cast htN
  have hl0 : 0 ≤ (t : ℝ) / N := div_nonneg (Nat.cast_nonneg t) hNR.le
  have hl1 : (t : ℝ) / N ≤ 1 := (div_le_one hNR).mpr htR
  have hmul : (t : ℝ) * (q - a) =
      (t : ℝ) / N * (rT - ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ))) := by
    rw [← hq, mul_comm (q - a) (N : ℝ), ← mul_assoc, div_mul_cancel₀ _ hNR.ne']
  obtain ⟨z1, z2⟩ := abs_le.mp hz
  obtain ⟨T1, T2⟩ := abs_le.mp hT
  obtain ⟨d1, d2⟩ := abs_le.mp hdev
  have p1 := mul_nonneg hl0 (by linarith : 0 ≤ B0 - (rT - ρ))
  have p2 := mul_nonneg hl0 (by linarith : 0 ≤ B0 + (rT - ρ))
  have p3 := mul_nonneg (by linarith : 0 ≤ 1 - (t : ℝ) / N)
    (by linarith : 0 ≤ B0 - ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - ρ))
  have p4 := mul_nonneg (by linarith : 0 ≤ 1 - (t : ℝ) / N)
    (by linarith : 0 ≤ B0 + ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - ρ))
  rw [abs_le]
  constructor <;> nlinarith

/-- The level of a vertex of a `horizontalFirst` path. -/
private theorem hf_level (p : Lattice) (e : ℕ × ℕ) (i : Fin (e.1 + e.2 + 1)) :
    ((horizontalFirst p e).vertex i).1 + ((horizontalFirst p e).vertex i).2 =
      p.1 + p.2 + (i.val : ℤ) := by
  show p.1 + ((min i.val e.1 : ℕ) : ℤ) + (p.2 + ((i.val - e.1 : ℕ) : ℤ)) = _
  have := i.isLt
  omega

/-- **The arrival piece, item (C4).** -/
theorem coarse_arrival_piece (ω : Environment) (T θ₁ : ℝ) (m1 K1 : ℕ) (Q : Set Lattice)
    (a Cm t Nl ρ B0 B : ℝ) :
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
  5 * θ₁ ≤ a → 5 * θ₁ ≤ 1 - a → B0 + (W0 : ℝ) + (L : ℝ) ≤ B →
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
  ∀ (z v : Lattice) (n : ℕ), z ∈ Q → ¬ (reach ω T z).Finite → boxFree ω T v →
    v.1 + v.2 = z.1 + z.2 + (n : ℤ) → L ≤ n → (n : ℝ) ≤ Nl →
    |(1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ) - ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ))| ≤
      4 * θ₁ * (n : ℝ) →
    |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - ρ| ≤ B0 →
    |(1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ) - ρ| ≤ B0 →
    (∀ y : Lattice, z.1 + z.2 ≤ y.1 + y.2 → y.1 + y.2 ≤ v.1 + v.2 →
      |(1 - a) * (y.1 : ℝ) - a * (y.2 : ℝ) - ρ| ≤ B → y ∈ Q) →
    ∃ (d : ℕ × ℕ) (p : Path z d), z + ((d.1 : ℤ), (d.2 : ℤ)) = v ∧
      -2 * Cm * (n : ℝ) - t / 2 ≤ pathWeight ω p ∧
      ∀ i, |(1 - a) * ((p.vertex i).1 : ℝ) - a * ((p.vertex i).2 : ℝ) - ρ| ≤ B := by
  intro reach reachBack Ntr W0 L r0 D1 d0 c0 collar Egeo boxFree hθ hθ' hm hK hE h5a h5b hB
    hE3 z v n hzQ hnt hbox hlev hLn hnl hR hzρ hvρ hQm
  have hN : (v.1 - z.1 + (v.2 - z.2)).toNat = n := by omega
  have hLpos : 0 < L := by
    show 0 < ⌈4 * ((W0 : ℝ) + 2) / θ₁⌉₊
    exact Nat.ceil_pos.mpr (by positivity)
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlevR : (v.1 : ℝ) + v.2 = z.1 + z.2 + n := by exact_mod_cast hlev
  have hx1R : ((v.1 - z.1 : ℤ) : ℝ) = ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ) -
      ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ))) + a * n := by
    push_cast
    linear_combination a * hlevR
  have hx2R : ((v.2 - z.2 : ℤ) : ℝ) = n - ((v.1 - z.1 : ℤ) : ℝ) := by
    push_cast
    linarith
  obtain ⟨R1, R2⟩ := abs_le.mp hR
  have han := mul_le_mul_of_nonneg_right h5a hnR.le
  have hbn := mul_le_mul_of_nonneg_right h5b hnR.le
  set q : ℝ := ((v.1 - z.1 : ℤ) : ℝ) / (n : ℝ) with hq
  have hq1 : θ₁ ≤ q := by
    rw [hq, le_div_iff₀ hnR, hx1R]
    nlinarith
  have hq2 : q ≤ 1 - θ₁ := by
    rw [hq, div_le_iff₀ hnR, hx1R]
    nlinarith
  have hqline : (q - a) * (n : ℝ) = (1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ) -
      ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)) := by
    rw [hq, sub_mul, div_mul_cancel₀ _ hnR.ne', hx1R]
    ring
  have hz1 : z.1 ≤ v.1 := by
    have h : (0 : ℝ) ≤ ((v.1 - z.1 : ℤ) : ℝ) := by rw [hx1R]; nlinarith
    have : (0 : ℤ) ≤ v.1 - z.1 := by exact_mod_cast h
    omega
  have hz2 : z.2 ≤ v.2 := by
    have h : (0 : ℝ) ≤ ((v.2 - z.2 : ℤ) : ℝ) := by rw [hx2R, hx1R]; nlinarith
    have : (0 : ℤ) ≤ v.2 - z.2 := by exact_mod_cast h
    omega
  have hline : ∀ (y : Lattice) (s : ℕ) (Dv : ℝ), s ≤ n → y.1 + y.2 = z.1 + z.2 + (s : ℤ) →
      |deviation z q s y| ≤ Dv → |(1 - a) * (y.1 : ℝ) - a * (y.2 : ℝ) - ρ| ≤ B0 + Dv :=
    fun y s Dv hs hy hd => line_transverse_le a q ρ B0 Dv _ z y s n hnpos hs hqline hzρ hvρ hy hd
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hmarg : ∀ y : Lattice, z.1 + z.2 ≤ y.1 + y.2 → y.1 + y.2 ≤ v.1 + v.2 →
      |deviation z q (y.1 + y.2 - (z.1 + z.2)).toNat y| ≤ (W0 : ℝ) → y ∈ Q := by
    intro y h1 h2 hd
    refine hQm y h1 h2 ?_
    have := hline y _ (W0 : ℝ) (by omega) (by omega) hd
    linarith
  have A := stair_greedy_arrival ω T θ₁ m1 K1 Q hθ hθ' hm hK hE z v hzQ hnt hz1 hz2
    (by rw [hN]; exact hLn) (by rw [hN]; exact hq1) (by rw [hN]; exact hq2) hbox
    (by rw [hN]; exact hmarg)
  dsimp only at A
  rw [hN] at A
  obtain ⟨hx1, hx2, he, hxs, hbadx, hbadhf, hdevhf⟩ := A
  set X : ℕ → Lattice := vertex z q {y | (reach ω T y).Finite}
  set e : ℕ × ℕ := ((v.1 - (X (n - L)).1).toNat, (v.2 - (X (n - L)).2).toNat)
  have hx1' : (X (n - L)).1 ≤ v.1 := hx1
  have hx2' : (X (n - L)).2 ≤ v.2 := hx2
  have he' : e.1 + e.2 = L := he
  have hxs' : ∀ s, s ≤ n - L → X s ∈ Q ∧ |deviation z q s (X s)| ≤ (W0 : ℝ) := hxs
  have hbadx' : ∀ s, s < n - L → -T ≤ ω (X s) := hbadx
  have hbadhf' : ∀ i : Fin (e.1 + e.2 + 1), i.val < e.1 + e.2 →
      -T ≤ ω ((horizontalFirst (X (n - L)) e).vertex i) := hbadhf
  have hdevhf' : ∀ i : Fin (e.1 + e.2 + 1),
      |deviation z q (n - L + i.val) ((horizontalFirst (X (n - L)) e).vertex i)| ≤
        (W0 : ℝ) + (L : ℝ) := hdevhf
  have hlevX : ∀ s, (X s).1 + (X s).2 = z.1 + z.2 + (s : ℤ) :=
    GreedyAttachment.level z q {y | (reach ω T y).Finite}
  have hhfB : ∀ i : Fin (e.1 + e.2 + 1),
      |(1 - a) * (((horizontalFirst (X (n - L)) e).vertex i).1 : ℝ) -
        a * (((horizontalFirst (X (n - L)) e).vertex i).2 : ℝ) - ρ| ≤ B := by
    intro i
    have hi := i.isLt
    have := hline _ (n - L + i.val) ((W0 : ℝ) + L) (by omega)
      (by rw [hf_level, hlevX]; omega) (hdevhf' i)
    linarith
  have hhfQ : ∀ i : Fin (e.1 + e.2 + 1), (horizontalFirst (X (n - L)) e).vertex i ∈ Q := by
    intro i
    have hi := i.isLt
    have hl := hf_level (X (n - L)) e i
    have hp := hlevX (n - L)
    exact hQm _ (by omega) (by omega) (hhfB i)
  have hxB : ∀ s, s ≤ n - L →
      |(1 - a) * ((X s).1 : ℝ) - a * ((X s).2 : ℝ) - ρ| ≤ B := by
    intro s hs
    have := hline _ s (W0 : ℝ) (by omega) (hlevX s) (hxs' s hs).2
    linarith
  have hw3 : -2 * Cm * (n : ℝ) - t / 2 ≤
      (∑ s ∈ Finset.range (n - L), ω (X s)) + pathWeight ω (horizontalFirst (X (n - L)) e) := by
    have h := hE3 z v hz1 hz2
    dsimp only at h
    rw [hN] at h
    exact h hLn hnl hx1' hx2' (fun s hs => (hxs' s hs).1) hhfQ hbadx' hbadhf'
  obtain ⟨d₁, p₁, hend₁, hlen₁, hv₁, hw₁⟩ :=
    exists_path_of_seq X (n - L) (fun s _ => GreedyAttachment.step z q _ s)
  have hpend : X (n - L) + ((e.1 : ℤ), (e.2 : ℤ)) = v := by
    apply Prod.ext
    · show (X (n - L)).1 + ((v.1 - (X (n - L)).1).toNat : ℤ) = v.1
      omega
    · show (X (n - L)).2 + ((v.2 - (X (n - L)).2).toNat : ℤ) = v.2
      omega
  obtain ⟨D, r, hD, hrw, hrB⟩ := exists_path_join ω
    (fun y => (1 - a) * (y.1 : ℝ) - a * (y.2 : ℝ) - ρ) B
    (∑ s ∈ Finset.range (n - L), ω (X s))
    (pathWeight ω (horizontalFirst (X (n - L)) e)) z (X (n - L)) v
    ⟨d₁, p₁, hend₁, (hw₁ ω).ge, fun i => by
      rw [hv₁ i]
      exact hxB _ (by have := i.isLt; omega)⟩
    ⟨e, horizontalFirst (X (n - L)) e, hpend, le_rfl, hhfB⟩
  exact ⟨D, r, hD, by linarith, hrB⟩

/-- Splitting a sum over `[0, n)` at `α ≤ β`. -/
private theorem sum_split3 (f : ℕ → ℝ) (n α β : ℕ) (h1 : α ≤ β) (h2 : β ≤ n) :
    ∑ s ∈ Finset.range n, f s = ∑ s ∈ Finset.range α, f s +
      ∑ s ∈ Finset.range (β - α), f (α + s) + ∑ s ∈ Finset.range (n - β), f (β + s) := by
  conv_lhs => rw [show n = α + (β - α) + (n - β) by omega]
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have h : α + (β - α) = β := by omega
  rw [h]

/-- A sum of `n` terms each at most `c`. -/
private theorem sum_range_le_mul (f : ℕ → ℝ) (n : ℕ) (c : ℝ) (h : ∀ s < n, f s ≤ c) :
    ∑ s ∈ Finset.range n, f s ≤ n * c := by
  calc ∑ s ∈ Finset.range n, f s ≤ ∑ _s ∈ Finset.range n, c :=
        Finset.sum_le_sum fun s hs => h s (Finset.mem_range.mp hs)
    _ = n * c := by simp

/-- **The trimmed crossing, item (C2).** -/
theorem coarse_trim_piece (ω : Environment) (T θ₁ : ℝ) (m1 K1 : ℕ) (Q : Set Lattice)
    (a ρ B w Wx : ℝ) :
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
  0 < θ₁ → θ₁ ≤ 1 / 10 → 1 ≤ m1 → 1 ≤ K1 → Egeo ω T Q → 0 ≤ w →
  ∀ (x₀ : Lattice) (d : ℕ × ℕ) (x : Path x₀ d), 2 * r0 + 1 ≤ d.1 + d.2 →
    (∀ i, x.vertex i ∈ Q) → (∀ i, ω (x.vertex i) ≤ w) →
    (∀ i, |(1 - a) * ((x.vertex i).1 : ℝ) - a * ((x.vertex i).2 : ℝ) - ρ| ≤ B) →
    Wx ≤ pathWeight ω x →
    ∃ (v v' : Lattice) (α β : ℕ), α ≤ r0 ∧ d.1 + d.2 ≤ β + r0 ∧ β ≤ d.1 + d.2 ∧
      v.1 + v.2 = x₀.1 + x₀.2 + (α : ℤ) ∧ v'.1 + v'.2 = x₀.1 + x₀.2 + (β : ℤ) ∧
      (∃ i, x.vertex i = v) ∧ (∃ i, x.vertex i = v') ∧
      boxFree ω T v ∧ ¬ (reach ω T v').Finite ∧
      ∃ (e : ℕ × ℕ) (p : Path v e), v + ((e.1 : ℤ), (e.2 : ℤ)) = v' ∧
        Wx - 2 * (r0 : ℝ) * w ≤ pathWeight ω p ∧
        ∀ i, |(1 - a) * ((p.vertex i).1 : ℝ) - a * ((p.vertex i).2 : ℝ) - ρ| ≤ B := by
  intro reach reachBack Ntr W0 L r0 D1 d0 c0 collar Egeo boxFree hθ hθ' hm hK hE hw0 x₀ d x hl'
    hxQ hxw hxB hWx
  obtain ⟨y, hy0, hyv, hystep, hyw⟩ := exists_seq_of_path x
  have hyc := seq_coords y (d.1 + d.2) hystep
  obtain ⟨⟨ia, -, hia1, hbox⟩, -, -⟩ := stair_trim ω T θ₁ m1 K1 Q hθ hθ' hm hK hE x₀ d x 0
    (by show 0 + r0 ≤ d.1 + d.2; omega) (fun i _ _ => hxQ i)
  obtain ⟨-, ⟨ib, hib0, -, hnt⟩, -⟩ := stair_trim ω T θ₁ m1 K1 Q hθ hθ' hm hK hE x₀ d x
    (d.1 + d.2 - r0) (by show d.1 + d.2 - r0 + r0 ≤ d.1 + d.2; omega) (fun i _ _ => hxQ i)
  have hia1' : ia.val ≤ 0 + r0 := hia1
  have hib0' : d.1 + d.2 - r0 ≤ ib.val := hib0
  have hbox' : boxFree ω T (y ia.val) := by rw [← hyv ia]; exact hbox
  have hnt' : ¬ (reach ω T (y ib.val)).Finite := by rw [← hyv ib]; exact hnt
  have hib2 := ib.isLt
  have hab : ia.val ≤ ib.val := by omega
  have hyQ : ∀ s ≤ d.1 + d.2, ω (y s) ≤ w ∧
      |(1 - a) * ((y s).1 : ℝ) - a * ((y s).2 : ℝ) - ρ| ≤ B := fun s hs => by
    have h : x.vertex ⟨s, by omega⟩ = y s := hyv ⟨s, by omega⟩
    rw [← h]
    exact ⟨hxw _, hxB _⟩
  obtain ⟨e, p, hend, hlen, hpv, hpw⟩ := exists_path_of_seq (fun s => y (ia.val + s))
    (ib.val - ia.val) (fun s hs => hystep (ia.val + s) (by omega))
  have hend' : y ia.val + ((e.1 : ℤ), (e.2 : ℤ)) = y ib.val := by
    rw [← Nat.add_sub_cancel' hab]
    exact hend
  have hsplit : ∑ s ∈ Finset.range (d.1 + d.2), ω (y s) =
      ∑ s ∈ Finset.range ia.val, ω (y s) +
        ∑ s ∈ Finset.range (ib.val - ia.val), ω (y (ia.val + s)) +
        ∑ s ∈ Finset.range (d.1 + d.2 - ib.val), ω (y (ib.val + s)) :=
    sum_split3 (fun s => ω (y s)) _ _ _ hab (by omega)
  have hA : ∑ s ∈ Finset.range ia.val, ω (y s) ≤ (ia.val : ℝ) * w :=
    sum_range_le_mul (fun s => ω (y s)) _ _ fun s hs => (hyQ s (by omega)).1
  have hC : ∑ s ∈ Finset.range (d.1 + d.2 - ib.val), ω (y (ib.val + s)) ≤
      ((d.1 + d.2 - ib.val : ℕ) : ℝ) * w :=
    sum_range_le_mul (fun s => ω (y (ib.val + s))) _ _ fun s hs => (hyQ _ (by omega)).1
  have hpw' : pathWeight ω p = ∑ s ∈ Finset.range (ib.val - ia.val), ω (y (ia.val + s)) :=
    hpw ω
  have hxw' : pathWeight ω x = ∑ s ∈ Finset.range (d.1 + d.2), ω (y s) := hyw ω
  have hia : (ia.val : ℝ) ≤ r0 := by exact_mod_cast (by omega : ia.val ≤ r0)
  have hic : ((d.1 + d.2 - ib.val : ℕ) : ℝ) ≤ r0 := by
    exact_mod_cast (by omega : d.1 + d.2 - ib.val ≤ r0)
  have hm1 := mul_le_mul_of_nonneg_right hia hw0
  have hm2 := mul_le_mul_of_nonneg_right hic hw0
  refine ⟨y ia.val, y ib.val, ia.val, ib.val, by omega, by omega, by omega, ?_, ?_,
    ⟨ia, hyv ia⟩, ⟨ib, hyv ib⟩, hbox', hnt', e, p, hend', ?_, fun i => ?_⟩
  · rw [← hy0]; exact (hyc _ (by omega)).2.2
  · rw [← hy0]; exact (hyc _ (by omega)).2.2
  · rw [hpw']
    linarith
  · rw [hpv i]
    exact (hyQ (ia.val + i.val) (by have := i.isLt; omega)).2

end LPPDifferentiability

end
