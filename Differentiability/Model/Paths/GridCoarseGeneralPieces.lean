/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.StairGreedyBackward
public import LPP_Foundations.Model.Paths.WeightConcat
import Mathlib.Tactic

/-! # Deterministic pieces for the coarse scale of the general Lemma 5.7

Helpers for the coarse piece of item (C4) of Section B.3 of the differentiability preprint:

* `exists_path_of_seq`, `exists_seq_of_path`: a sequence with up-right steps is a `Path`, with
  vertex `k` equal to the `k`-th term and weight the sum of the first `n` terms; conversely.
* `exists_path_join`: joining two paths with a common endpoint adds their weights and keeps a
  bound on every vertex.
* `not_trapped_of_long_seq`: a vertex from which an up-right path of `n + 1 ≥ m1²` vertices
  collects no very bad vertex has an infinite reach set when every finite reach set has fewer
  than `m1²` elements (the argument of item (C4) for the part of `γ^u` below `u`).
* `greedy_forward_in_region`, `greedy_backward_in_region`: the greedy paths of
  Lemma B.5 (ii) stay in the region `Q` when every greedy vertex within deviation
  `W0 + 1` of its line lies in `Q`; the step from one vertex to the next changes the deviation
  by at most `1`.
-/

public section

namespace LPPDifferentiability
open GreedyAttachment (vertex deviation)

/-- Coordinates and levels along a sequence with up-right steps. -/
theorem seq_coords (y : ℕ → Lattice) (n : ℕ)
    (hstep : ∀ s < n, y (s + 1) = y s + (1, 0) ∨ y (s + 1) = y s + (0, 1)) :
    ∀ s ≤ n, (y 0).1 ≤ (y s).1 ∧ (y 0).2 ≤ (y s).2 ∧
      (y s).1 + (y s).2 = (y 0).1 + (y 0).2 + (s : ℤ) := by
  intro s
  induction s with
  | zero => intro _; simp
  | succ s ih =>
    intro hs
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    rcases hstep s (by omega) with h | h <;> rw [h] <;>
      simp only [Prod.fst_add, Prod.snd_add] <;> push_cast <;> omega

/-- A sequence with up-right steps on `[0, n]` is a path of length `n`. -/
theorem exists_path_of_seq (y : ℕ → Lattice) (n : ℕ)
    (hstep : ∀ s < n, y (s + 1) = y s + (1, 0) ∨ y (s + 1) = y s + (0, 1)) :
    ∃ (d : ℕ × ℕ) (p : Path (y 0) d), y 0 + ((d.1 : ℤ), (d.2 : ℤ)) = y n ∧ d.1 + d.2 = n ∧
      (∀ i : Fin (d.1 + d.2 + 1), p.vertex i = y i.val) ∧
      ∀ ω : Environment, pathWeight ω p = ∑ s ∈ Finset.range n, ω (y s) := by
  obtain ⟨h1, h2, h3⟩ := seq_coords y n hstep n le_rfl
  let d : ℕ × ℕ := (((y n).1 - (y 0).1).toNat, ((y n).2 - (y 0).2).toNat)
  have hlen : d.1 + d.2 = n := by
    show ((y n).1 - (y 0).1).toNat + ((y n).2 - (y 0).2).toNat = n
    omega
  have hend : y 0 + ((d.1 : ℤ), (d.2 : ℤ)) = y n := by
    apply Prod.ext
    · show (y 0).1 + (((y n).1 - (y 0).1).toNat : ℤ) = (y n).1
      omega
    · show (y 0).2 + (((y n).2 - (y 0).2).toNat : ℤ) = (y n).2
      omega
  let p : Path (y 0) d :=
    { vertex := fun i => y i.val
      start := by simp
      finish := by
        show y (d.1 + d.2) = _
        rw [hlen, hend]
      step := fun i => by
        show y (i.val + 1) = y i.val + (1, 0) ∨ y (i.val + 1) = y i.val + (0, 1)
        exact hstep i.val (by have := i.isLt; omega) }
  refine ⟨d, p, hend, hlen, fun i => rfl, fun ω => ?_⟩
  unfold pathWeight
  rw [← hlen]
  exact Fin.sum_univ_eq_sum_range (fun s => ω (y s)) (d.1 + d.2)

/-- The vertices of a path, extended to a sequence. -/
theorem exists_seq_of_path {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    ∃ y : ℕ → Lattice, y 0 = u ∧ (∀ i : Fin (d.1 + d.2 + 1), p.vertex i = y i.val) ∧
      (∀ s < d.1 + d.2, y (s + 1) = y s + (1, 0) ∨ y (s + 1) = y s + (0, 1)) ∧
      ∀ ω : Environment, pathWeight ω p = ∑ s ∈ Finset.range (d.1 + d.2), ω (y s) := by
  let y : ℕ → Lattice := fun s => p.vertex ⟨min s (d.1 + d.2), by omega⟩
  have hv : ∀ i : Fin (d.1 + d.2 + 1), p.vertex i = y i.val := fun i => by
    show p.vertex i = p.vertex ⟨min i.val (d.1 + d.2), by omega⟩
    congr 1
    apply Fin.ext
    have := i.isLt
    show i.val = min i.val (d.1 + d.2)
    omega
  refine ⟨y, ?_, hv, fun s hs => ?_, fun ω => ?_⟩
  · show p.vertex ⟨min 0 (d.1 + d.2), by omega⟩ = u
    rw [show (⟨min 0 (d.1 + d.2), by omega⟩ : Fin (d.1 + d.2 + 1)) = 0 from Fin.ext (by simp)]
    exact p.start
  · have h := p.step ⟨s, hs⟩
    rw [hv, hv] at h
    exact h
  · unfold pathWeight
    rw [← Fin.sum_univ_eq_sum_range (fun s => ω (y s)) (d.1 + d.2)]
    apply Finset.sum_congr rfl
    intro i _
    rw [hv]
    rfl

/-- Every vertex of a concatenation is a vertex of one of the two pieces. -/
private theorem concat_vertex_cases' {u : Lattice} {d e : ℕ × ℕ} (p : Path u d)
    (q : Path (u + ((d.1 : ℤ), (d.2 : ℤ))) e) (k : Fin ((d + e).1 + (d + e).2 + 1)) :
    (∃ i, (p.concat q).vertex k = p.vertex i) ∨ ∃ i, (p.concat q).vertex k = q.vertex i := by
  have hk := k.isLt
  simp only [Prod.fst_add, Prod.snd_add] at hk
  by_cases h : k.val < d.1 + d.2
  · exact Or.inl ⟨⟨k.val, by omega⟩, by simp [Path.concat, Path.concatVertex, h]⟩
  · exact Or.inr ⟨⟨k.val - (d.1 + d.2), by omega⟩, by simp [Path.concat, Path.concatVertex, h]⟩

/-- Joining two paths with a common endpoint: the weights add and a bound on every vertex is
kept. -/
theorem exists_path_join (ω : Environment) (f : Lattice → ℝ) (B W₁ W₂ : ℝ) (u v w : Lattice)
    (h₁ : ∃ (d : ℕ × ℕ) (p : Path u d), u + ((d.1 : ℤ), (d.2 : ℤ)) = v ∧
      W₁ ≤ pathWeight ω p ∧ ∀ i, |f (p.vertex i)| ≤ B)
    (h₂ : ∃ (e : ℕ × ℕ) (q : Path v e), v + ((e.1 : ℤ), (e.2 : ℤ)) = w ∧
      W₂ ≤ pathWeight ω q ∧ ∀ i, |f (q.vertex i)| ≤ B) :
    ∃ (D : ℕ × ℕ) (r : Path u D), u + ((D.1 : ℤ), (D.2 : ℤ)) = w ∧
      W₁ + W₂ ≤ pathWeight ω r ∧ ∀ i, |f (r.vertex i)| ≤ B := by
  obtain ⟨d, p, hv, hp1, hp2⟩ := h₁
  obtain ⟨e, q, hw, hq1, hq2⟩ := h₂
  subst hv
  refine ⟨d + e, p.concat q, ?_, ?_, fun k => ?_⟩
  · rw [← hw]
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add] <;> omega
  · rw [pathWeight_concat]
    linarith
  · rcases concat_vertex_cases' p q k with ⟨i, hi⟩ | ⟨i, hi⟩ <;> rw [hi]
    · exact hp2 i
    · exact hq2 i

/-- **The argument of item (C4) below `u`.** If an up-right path of `n + 1` vertices starting at
`y 0` collects no very bad vertex, then all its vertices lie in the reach set of `y 0`; so when
`m1² ≤ n + 1` and every finite reach set of `y 0` has fewer than `m1²` elements, the reach set
of `y 0` is infinite. -/
theorem not_trapped_of_long_seq (ω : Environment) (T : ℝ) (m1 : ℕ) :
    let reach : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
      {y | ∃ (d : ℕ × ℕ) (q : Path z d), z + ((d.1 : ℤ), (d.2 : ℤ)) = y ∧
        ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
    ∀ (y : ℕ → Lattice) (n : ℕ),
      (∀ s < n, y (s + 1) = y s + (1, 0) ∨ y (s + 1) = y s + (0, 1)) →
      (∀ s < n, -T ≤ ω (y s)) → m1 ^ 2 ≤ n + 1 →
      ((reach ω T (y 0)).Finite → (reach ω T (y 0)).ncard < m1 ^ 2) →
      ¬ (reach ω T (y 0)).Finite := by
  intro reach y n hstep hbad hn hfin hF
  have hmem : ∀ s ≤ n, y s ∈ reach ω T (y 0) := by
    intro s hs
    obtain ⟨d, p, hend, hlen, hv, -⟩ := exists_path_of_seq y s (fun t ht => hstep t (by omega))
    show ∃ (d : ℕ × ℕ) (q : Path (y 0) d), y 0 + ((d.1 : ℤ), (d.2 : ℤ)) = y s ∧
      ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)
    exact ⟨d, p, hend, fun i hi => by rw [hv i]; exact hbad _ (by omega)⟩
  have hlev := seq_coords y n hstep
  have hinj : Set.InjOn y (Finset.range (n + 1) : Set ℕ) := by
    intro s hs t ht hst
    simp only [Finset.coe_range, Set.mem_Iio] at hs ht
    have h1 := (hlev s (by omega)).2.2
    have h2 := (hlev t (by omega)).2.2
    rw [hst] at h1
    omega
  have hsub : (((Finset.range (n + 1)).image y : Finset Lattice) : Set Lattice) ⊆
      reach ω T (y 0) := by
    intro z hz
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    exact hmem s (by omega)
  have hcard : ((Finset.range (n + 1)).image y).card = n + 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hle := Set.ncard_le_ncard hsub hF
  rw [Set.ncard_coe_finset, hcard] at hle
  have := hfin hF
  omega

/-- One greedy step changes the deviation from the line by at most `1`. -/
theorem greedy_deviation_succ_le (z : Lattice) (q : ℝ) (V : Set Lattice) (s : ℕ)
    (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    |deviation z q (s + 1) (vertex z q V (s + 1))| ≤ |deviation z q s (vertex z q V s)| + 1 := by
  have hD1 := le_abs_self (((vertex z q V s).1 : ℝ) - z.1 - (s : ℝ) * q)
  have hD2 := neg_abs_le (((vertex z q V s).1 : ℝ) - z.1 - (s : ℝ) * q)
  rcases GreedyAttachment.step z q V s with h | h <;> rw [h] <;> unfold deviation <;>
    simp only [Prod.fst_add, Int.cast_add, Int.cast_one, Int.cast_zero, Nat.cast_add,
      Nat.cast_one] <;> rw [abs_le] <;> constructor <;> linarith

/-- **Forward greedy path inside the region.** -/
theorem greedy_forward_in_region (ω : Environment) (T θ₁ : ℝ) (m1 K1 : ℕ) (Q : Set Lattice) :
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
  ∀ z ∈ Q, ¬ (reach ω T z).Finite → ∀ q : ℝ, θ₁ ≤ q → q ≤ 1 - θ₁ → ∀ n : ℕ,
    (∀ s, s ≤ n →
      |deviation z q s (vertex z q {y | (reach ω T y).Finite} s)| ≤ (W0 : ℝ) + 1 →
      vertex z q {y | (reach ω T y).Finite} s ∈ Q) →
    ∀ s, s ≤ n →
      vertex z q {y | (reach ω T y).Finite} s ∈ Q ∧
      ¬ (reach ω T (vertex z q {y | (reach ω T y).Finite} s)).Finite ∧
      -T ≤ ω (vertex z q {y | (reach ω T y).Finite} s) ∧
      |deviation z q s (vertex z q {y | (reach ω T y).Finite} s)| ≤ (W0 : ℝ) := by
  intro reach reachBack Ntr W0 L r0 D1 d0 c0 collar Egeo hθ hθ' hm hK hE z hz hnt q hq1 hq2 n
    hmar
  have hQ : ∀ s, s ≤ n → vertex z q {y | (reach ω T y).Finite} s ∈ Q := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro hs
      cases s with
      | zero => simpa using hz
      | succ s =>
        have hprev : |deviation z q s (vertex z q {y | (reach ω T y).Finite} s)| ≤ (W0 : ℝ) :=
          (stair_greedy_forward ω T θ₁ m1 K1 Q hθ hθ' hm hK hE z hz hnt q hq1 hq2 s
            (fun i hi => ih i (by omega) (by omega)) s le_rfl).2.2
        exact hmar (s + 1) hs ((greedy_deviation_succ_le z q _ s (by linarith)
          (by linarith)).trans (by linarith))
  intro s hs
  obtain ⟨h1, h2, h3⟩ :=
    stair_greedy_forward ω T θ₁ m1 K1 Q hθ hθ' hm hK hE z hz hnt q hq1 hq2 n hQ s hs
  exact ⟨hQ s hs, h1, h2, h3⟩

/-- **Backward greedy path inside the region.** -/
theorem greedy_backward_in_region (ω : Environment) (T θ₁ : ℝ) (m1 K1 : ℕ) (Q : Set Lattice) :
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
  let Wb : Set Lattice := {y | ω (-y) < -T ∨ (reachBack ω T (-y)).Finite}
  0 < θ₁ → θ₁ ≤ 1 / 10 → 1 ≤ m1 → 1 ≤ K1 → Egeo ω T Q →
  ∀ z ∈ Q, -T ≤ ω z → ¬ (reachBack ω T z).Finite → ∀ q : ℝ, θ₁ ≤ q → q ≤ 1 - θ₁ →
    ∀ n : ℕ, (∀ s, s ≤ n → |deviation (-z) q s (vertex (-z) q Wb s)| ≤ (W0 : ℝ) + 1 →
      -vertex (-z) q Wb s ∈ Q) →
    ∀ s, s ≤ n →
      -vertex (-z) q Wb s ∈ Q ∧ -T ≤ ω (-vertex (-z) q Wb s) ∧
      ¬ (reachBack ω T (-vertex (-z) q Wb s)).Finite ∧
      |deviation (-z) q s (vertex (-z) q Wb s)| ≤ (W0 : ℝ) := by
  intro reach reachBack Ntr W0 L r0 D1 d0 c0 collar Egeo Wb hθ hθ' hm hK hE z hz hzT hzB q hq1
    hq2 n hmar
  have hQ : ∀ s, s ≤ n → -vertex (-z) q Wb s ∈ Q := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro hs
      cases s with
      | zero => simpa using hz
      | succ s =>
        have hprev : |deviation (-z) q s (vertex (-z) q Wb s)| ≤ (W0 : ℝ) :=
          (stair_greedy_backward ω T θ₁ m1 K1 Q hθ hθ' hm hK hE z hz hzT hzB q hq1
            hq2 s (fun i hi => ih i (by omega) (by omega)) s le_rfl).2.2
        exact hmar (s + 1) hs ((greedy_deviation_succ_le (-z) q _ s (by linarith)
          (by linarith)).trans (by linarith))
  intro s hs
  obtain ⟨h1, h2, h3⟩ :=
    stair_greedy_backward ω T θ₁ m1 K1 Q hθ hθ' hm hK hE z hz hzT hzB q hq1 hq2 n hQ s hs
  exact ⟨hQ s hs, h1, h2, h3⟩

end LPPDifferentiability

end
