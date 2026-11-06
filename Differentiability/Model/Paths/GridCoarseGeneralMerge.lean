/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.GridCoarseGeneralArrival
public import Differentiability.Model.Paths.TransverseMerge
import Mathlib.Tactic

/-! # The greedy merge path and the tail of `γ^u` at the coarse scale

The last two pieces of item (C4) of Section B.3 of the differentiability preprint. From the
trimmed end `v'` of the
crossing, the greedy path runs along the straight line toward the point on level `ℓ(v') + n`
with transverse coordinate `ρ − 2 W0 − 3`, `ρ = r(u)`. It is run for all `n` levels inside the
region; it starts to the `e₁` side of `γ^u` (a hypothesis here, proved by the caller from the
block geometry) and ends to the other side (proved here from the deviation bound `W0`), so by
Lemma B.5 (iv) it meets `γ^u` strictly inside. The greedy path up to the meeting
point and the segment of `γ^u` after it are joined into one path, with the weight bounds of the
staircase event (clause 4 for the greedy part, the caller's segment bound for `γ^u`).

`sq_le_two_pow_succ` is the bound `j² ≤ 2^(j+1)`, used for `j² w_{j,k} ≤ 2 s_k`.
-/

public section

namespace LPPDifferentiability
open GreedyAttachment (vertex deviation)

/-- `j² ≤ 2^(j+1)` for every natural number `j`. -/
theorem sq_le_two_pow_succ (j : ℕ) : j ^ 2 ≤ 2 ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rcases Nat.lt_or_ge j 3 with h | h
    · interval_cases j <;> norm_num
    · have h2 : (j + 1) ^ 2 ≤ 2 * j ^ 2 := by nlinarith
      calc (j + 1) ^ 2 ≤ 2 * j ^ 2 := h2
        _ ≤ 2 * 2 ^ (j + 1) := by omega
        _ = 2 ^ (j + 1 + 1) := by ring

/-- **The greedy merge path and the tail of `γ^u` (item (C4)).** -/
theorem coarse_merge_piece (ω : Environment) (T θ₁ : ℝ) (m1 K1 : ℕ) (Q : Set Lattice)
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
  0 < θ₁ → θ₁ ≤ 1 / 10 → 1 ≤ m1 → 1 ≤ K1 → Egeo ω T Q →
  5 * θ₁ ≤ a → 5 * θ₁ ≤ 1 - a → B0 + (W0 : ℝ) + 1 ≤ B → 2 * (W0 : ℝ) + 3 ≤ B0 →
  (∀ (z u : Lattice) (Λ : ℤ) (n : ℕ), z.1 + z.2 < Λ →
    ((Λ - (z.1 + z.2) : ℤ) : ℝ) ≤ Nl → (n : ℝ) ≤ Nl → u ∈ Q →
    let q : ℝ := ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) - 2 * (W0 : ℝ) - 3 +
      a * (Λ : ℝ) - (z.1 : ℝ)) / ((Λ - (z.1 + z.2) : ℤ) : ℝ)
    (∀ s, s ≤ n → GreedyAttachment.vertex z q {y | (reach ω T y).Finite} s ∈ Q) →
    (∀ s, s < n → -T ≤ ω (GreedyAttachment.vertex z q {y | (reach ω T y).Finite} s)) →
    -2 * Cm * (n : ℝ) - t / 2 ≤
      ∑ s ∈ Finset.range n, ω (GreedyAttachment.vertex z q {y | (reach ω T y).Finite} s)) →
  ∀ (u v' : Lattice) (g : ℕ → Lattice) (n : ℕ), u ∈ Q →
    (1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) = ρ → v' ∈ Q → ¬ (reach ω T v').Finite →
    0 < n → (n : ℝ) ≤ Nl →
    (∀ s < n, g (s + 1) = g s + (1, 0) ∨ g (s + 1) = g s + (0, 1)) →
    (g 0).1 + (g 0).2 = v'.1 + v'.2 →
    (∀ s ≤ n, |(1 - a) * ((g s).1 : ℝ) - a * ((g s).2 : ℝ) - ρ| ≤ (W0 : ℝ)) →
    (∀ i ≤ n, -2 * Cm * ((n - i : ℕ) : ℝ) - t / 2 ≤
      ∑ s ∈ Finset.range (n - i), ω (g (i + s))) →
    (1 - a) * ((g 0).1 : ℝ) - a * ((g 0).2 : ℝ) < (1 - a) * (v'.1 : ℝ) - a * (v'.2 : ℝ) →
    |(ρ - 2 * (W0 : ℝ) - 3) - ((1 - a) * (v'.1 : ℝ) - a * (v'.2 : ℝ))| ≤ 4 * θ₁ * (n : ℝ) →
    |(1 - a) * (v'.1 : ℝ) - a * (v'.2 : ℝ) - ρ| ≤ B0 →
    (∀ y : Lattice, v'.1 + v'.2 ≤ y.1 + y.2 → y.1 + y.2 ≤ v'.1 + v'.2 + (n : ℤ) →
      |(1 - a) * (y.1 : ℝ) - a * (y.2 : ℝ) - ρ| ≤ B → y ∈ Q) →
    ∃ (d : ℕ × ℕ) (p : Path v' d), v' + ((d.1 : ℤ), (d.2 : ℤ)) = g n ∧
      -2 * Cm * (n : ℝ) - t ≤ pathWeight ω p ∧
      ∀ i, |(1 - a) * ((p.vertex i).1 : ℝ) - a * ((p.vertex i).2 : ℝ) - ρ| ≤ B := by
  intro reach reachBack Ntr W0 L r0 D1 d0 c0 collar Egeo hθ hθ' hm hK hE h5a h5b hB hB0 hE4
    u v' g n huQ hρu hvQ hvnt hn hnl hgstep hglev hgr hgw hstart hslope hvρ hQm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hW0 : (0 : ℝ) ≤ W0 := Nat.cast_nonneg W0
  set Λ : ℤ := v'.1 + v'.2 + (n : ℤ) with hΛ
  have hΛn : ((Λ - (v'.1 + v'.2) : ℤ) : ℝ) = n := by
    simp only [hΛ, add_sub_cancel_left, Int.cast_natCast]
  have hΛR : (Λ : ℝ) = v'.1 + v'.2 + n := by
    simp only [hΛ, Int.cast_add, Int.cast_natCast]
  set q : ℝ := ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) - 2 * (W0 : ℝ) - 3 +
      a * (Λ : ℝ) - (v'.1 : ℝ)) / ((Λ - (v'.1 + v'.2) : ℤ) : ℝ) with hq
  have hqline : (q - a) * (n : ℝ) = (ρ - 2 * (W0 : ℝ) - 3) -
      ((1 - a) * (v'.1 : ℝ) - a * (v'.2 : ℝ)) := by
    rw [hq, hΛn, sub_mul, div_mul_cancel₀ _ hnR.ne', hΛR]
    linear_combination hρu
  obtain ⟨S1, S2⟩ := abs_le.mp hslope
  have han := mul_le_mul_of_nonneg_right h5a hnR.le
  have hbn := mul_le_mul_of_nonneg_right h5b hnR.le
  have hq1 : θ₁ ≤ q := le_of_mul_le_mul_right (by nlinarith) hnR
  have hq2 : q ≤ 1 - θ₁ := le_of_mul_le_mul_right (by nlinarith) hnR
  have hT : |(ρ - 2 * (W0 : ℝ) - 3) - ρ| ≤ B0 := by
    rw [abs_le]
    constructor <;> linarith
  have hlevG : ∀ s, (vertex v' q {y | (reach ω T y).Finite} s).1 +
      (vertex v' q {y | (reach ω T y).Finite} s).2 = v'.1 + v'.2 + (s : ℤ) :=
    GreedyAttachment.level v' q {y | (reach ω T y).Finite}
  have hline : ∀ (s : ℕ) (Dv : ℝ), s ≤ n →
      |deviation v' q s (vertex v' q {y | (reach ω T y).Finite} s)| ≤ Dv →
      |(1 - a) * ((vertex v' q {y | (reach ω T y).Finite} s).1 : ℝ) -
        a * ((vertex v' q {y | (reach ω T y).Finite} s).2 : ℝ) - ρ| ≤ B0 + Dv :=
    fun s Dv hs hd => line_transverse_le a q ρ B0 Dv _ v' _ s n hn hs hqline hvρ hT (hlevG s) hd
  have hmarG : ∀ s, s ≤ n →
      |deviation v' q s (vertex v' q {y | (reach ω T y).Finite} s)| ≤ (W0 : ℝ) + 1 →
      vertex v' q {y | (reach ω T y).Finite} s ∈ Q := fun s hs hd =>
    hQm _ (by rw [hlevG]; omega) (by rw [hlevG]; omega) (by have := hline s _ hs hd; linarith)
  have hG := greedy_forward_in_region ω T θ₁ m1 K1 Q hθ hθ' hm hK hE v' hvQ hvnt q hq1 hq2 n
    hmarG
  have hG' : ∀ s, s ≤ n → vertex v' q {y | (reach ω T y).Finite} s ∈ Q ∧
      ¬ (reach ω T (vertex v' q {y | (reach ω T y).Finite} s)).Finite ∧
      -T ≤ ω (vertex v' q {y | (reach ω T y).Finite} s) ∧
      |deviation v' q s (vertex v' q {y | (reach ω T y).Finite} s)| ≤ (W0 : ℝ) := hG
  have hGB : ∀ s, s ≤ n → |(1 - a) * ((vertex v' q {y | (reach ω T y).Finite} s).1 : ℝ) -
      a * ((vertex v' q {y | (reach ω T y).Finite} s).2 : ℝ) - ρ| ≤ B := fun s hs => by
    have := hline s _ hs (hG' s hs).2.2.2
    linarith
  obtain ⟨d, p, hend, hlen, hv, -⟩ := exists_path_of_seq (vertex v' q {y | (reach ω T y).Finite})
    n (fun s _ => GreedyAttachment.step v' q _ s)
  obtain ⟨d', p', hend', hlen', hv', -⟩ := exists_path_of_seq g n hgstep
  have e1 : (vertex v' q {y | (reach ω T y).Finite} 0).1 + (d.1 : ℤ) =
      (vertex v' q {y | (reach ω T y).Finite} n).1 := congrArg Prod.fst hend
  have e2 : (vertex v' q {y | (reach ω T y).Finite} 0).2 + (d.2 : ℤ) =
      (vertex v' q {y | (reach ω T y).Finite} n).2 := congrArg Prod.snd hend
  have e1' : (g 0).1 + (d'.1 : ℤ) = (g n).1 := congrArg Prod.fst hend'
  have e2' : (g 0).2 + (d'.2 : ℤ) = (g n).2 := congrArg Prod.snd hend'
  have hendsign : (1 - a) * ((vertex v' q {y | (reach ω T y).Finite} n).1 : ℝ) -
      a * ((vertex v' q {y | (reach ω T y).Finite} n).2 : ℝ) <
      (1 - a) * ((g n).1 : ℝ) - a * ((g n).2 : ℝ) := by
    have hdv := GreedyAttachment.transverse_deviation_eq v' _ q a n (hlevG n)
    obtain ⟨h1, h2⟩ := abs_le.mp (hG' n le_rfl).2.2.2
    obtain ⟨h3, h4⟩ := abs_le.mp (hgr n le_rfl)
    nlinarith
  obtain ⟨i, hi, -, hmeet⟩ := admissible_paths_merge a _ _ d d' p p' hglev.symm (by omega)
    hstart (by rw [e1, e2, e1', e2']; exact hendsign)
  rw [hv, hv'] at hmeet
  have hm' : vertex v' q {y | (reach ω T y).Finite} i = g i := hmeet
  have hin : i < n := by omega
  obtain ⟨d3, p3, hend3, hlen3, hv3, hw3⟩ := exists_path_of_seq
    (vertex v' q {y | (reach ω T y).Finite}) i (fun s _ => GreedyAttachment.step v' q _ s)
  have h4 := hE4 v' u Λ i (by omega) (by rw [hΛn]; exact hnl)
    (by have : (i : ℝ) ≤ n := by exact_mod_cast hin.le
        linarith) huQ
  dsimp only at h4
  have hw3' : -2 * Cm * (i : ℝ) - t / 2 ≤
      ∑ s ∈ Finset.range i, ω (vertex v' q {y | (reach ω T y).Finite} s) :=
    h4 (fun s hs => (hG' s (by omega)).1) (fun s hs => (hG' s (by omega)).2.2.1)
  obtain ⟨d4, p4, hend4, hlen4, hv4, hw4⟩ := exists_path_of_seq (fun s => g (i + s)) (n - i)
    (fun s hs => hgstep (i + s) (by omega))
  have hend4' : g i + ((d4.1 : ℤ), (d4.2 : ℤ)) = g n := by
    rw [← Nat.add_sub_cancel' hin.le]
    exact hend4
  obtain ⟨D, r, hD, hrw, hrB⟩ := exists_path_join ω
    (fun y => (1 - a) * (y.1 : ℝ) - a * (y.2 : ℝ) - ρ) B
    (-2 * Cm * (i : ℝ) - t / 2) (-2 * Cm * ((n - i : ℕ) : ℝ) - t / 2) v' (g i) (g n)
    ⟨d3, p3, by rw [← hm']; exact hend3, hw3'.trans_eq (hw3 ω).symm, fun k => by
      rw [hv3 k]
      exact hGB _ (by have := k.isLt; omega)⟩
    ⟨d4, p4, hend4', (hgw i hin.le).trans_eq (hw4 ω).symm, fun k => by
      rw [hv4 k]
      show |(1 - a) * ((g (i + k.val)).1 : ℝ) - a * ((g (i + k.val)).2 : ℝ) - ρ| ≤ B
      have := hgr (i + k.val) (by have := k.isLt; omega)
      linarith⟩
  have hcast : ((n - i : ℕ) : ℝ) = (n : ℝ) - (i : ℝ) := by
    rw [Nat.cast_sub hin.le]
  refine ⟨D, r, hD, ?_, hrB⟩
  rw [hcast] at hrw
  linarith

end LPPDifferentiability

end
