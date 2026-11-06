/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.StairGreedyForward
public import Differentiability.Model.Paths.StairGreedyBackward
public import LPP_Foundations.Model.Paths.ReflectedReverse
import Mathlib.Tactic

/-! # The fine piece of Lemma 5.7 (i) along `γ^u`, general weights

At a fine scale the piece of `γ^u` between two grid levels is a segment of the forward greedy path
(above `u`) or the reflected reverse of a backward greedy path (below `u`). It has defect at most
`C₁ j² w + 2 t` ((B.10) of the differentiability preprint) and stays within `C₁ j² w` of `r(u)`.
The circle of estimates between `Q_k` and the greedy deviation bound is closed by the lemma
`frame`. -/

public section

namespace LPPDifferentiability

private theorem seq_path (ω : Environment) (x : ℕ → Lattice)
    (hx : ∀ s, x (s + 1) = x s + (1, 0) ∨ x (s + 1) = x s + (0, 1)) (i n : ℕ)
    (z₀ z₁ : Lattice) (h₀ : z₀ = x i) (h₁ : z₁ = x (i + n)) :
    ∃ (D : ℕ × ℕ) (p : Path z₀ D), D.1 + D.2 = n ∧ z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
      (∀ j : Fin (D.1 + D.2 + 1), p.vertex j = x (i + j.val)) ∧
      pathWeight ω p = ∑ s ∈ Finset.range n, ω (x (i + s)) := by
  have hmono : ∀ m : ℕ, (x i).1 ≤ (x (i + m)).1 ∧ (x i).2 ≤ (x (i + m)).2 ∧
      (x (i + m)).1 + (x (i + m)).2 = (x i).1 + (x i).2 + (m : ℤ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      obtain ⟨_, _, _⟩ := ih
      rw [show i + (m + 1) = (i + m) + 1 by omega]
      rcases hx (i + m) with h | h <;> rw [h] <;>
        simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add, Nat.cast_one] <;> omega
  obtain ⟨_, _, m3⟩ := hmono n
  obtain ⟨D, hD1, hD2⟩ : ∃ D : ℕ × ℕ, (D.1 : ℤ) = (x (i + n)).1 - (x i).1 ∧
      (D.2 : ℤ) = (x (i + n)).2 - (x i).2 :=
    ⟨(((x (i + n)).1 - (x i).1).toNat, ((x (i + n)).2 - (x i).2).toNat),
      Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)⟩
  have hDn : D.1 + D.2 = n := by omega
  subst h₀
  subst h₁
  have hend : x i + ((D.1 : ℤ), (D.2 : ℤ)) = x (i + n) := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
  refine ⟨D, ⟨fun j => x (i + j.val), by simp, ?_, ?_⟩, hDn, hend, fun j => rfl, ?_⟩
  · show x (i + (Fin.last (D.1 + D.2)).val) = x i + ((D.1 : ℤ), (D.2 : ℤ))
    rw [Fin.val_last, hDn]
    exact hend.symm
  · intro j
    exact hx (i + j.val)
  · exact (Fin.sum_univ_eq_sum_range (fun s => ω (x (i + s))) (D.1 + D.2)).trans
      (by rw [hDn])

/-- The reflected reverse of that segment, an admissible path from `-x (i + n)` to `-x i`. -/
private theorem seq_path_rev (ω : Environment) (x : ℕ → Lattice)
    (hx : ∀ s, x (s + 1) = x s + (1, 0) ∨ x (s + 1) = x s + (0, 1)) (i n : ℕ)
    (z₀ z₁ : Lattice) (h₀ : z₀ = -x (i + n)) (h₁ : z₁ = -x i) :
    ∃ (D : ℕ × ℕ) (q : Path z₀ D), D.1 + D.2 = n ∧ z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
      (∀ j : Fin (D.1 + D.2 + 1), q.vertex j = -x (i + (n - j.val))) ∧
      pathWeight ω q = ∑ s ∈ Finset.range n, ω (-x (i + 1 + s)) := by
  obtain ⟨D, p, hDn, hD, hv, -⟩ := seq_path ω x hx i n (x i) (x (i + n)) rfl rfl
  obtain ⟨q, hq⟩ := p.exists_reflected_reverse
  have e : z₀ = -(x i + ((D.1 : ℤ), (D.2 : ℤ))) := by rw [h₀, hD]
  subst e
  have hqv : ∀ j : Fin (D.1 + D.2 + 1), q.vertex j = -x (i + (n - j.val)) := by
    intro j
    have hj := j.isLt
    rw [hq j, hv (Fin.rev j), show (Fin.rev j).val = n - j.val by rw [Fin.val_rev]; omega]
  refine ⟨D, q, hDn, ?_, hqv, ?_⟩
  · rw [h₁]
    apply Prod.ext <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] <;> omega
  · calc pathWeight ω q = ∑ j : Fin (D.1 + D.2), ω (-x (i + (n - j.val))) := by
          unfold pathWeight
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hqv j.castSucc, Fin.val_castSucc]
      _ = ∑ s ∈ Finset.range (D.1 + D.2), ω (-x (i + (n - s))) :=
          Fin.sum_univ_eq_sum_range (fun s => ω (-x (i + (n - s)))) (D.1 + D.2)
      _ = ∑ s ∈ Finset.range n, ω (-x (i + (n - s))) := by rw [hDn]
      _ = ∑ s ∈ Finset.range n, ω (-x (i + 1 + (n - 1 - s))) :=
          Finset.sum_congr rfl fun s hs => by
            have h := Finset.mem_range.mp hs
            rw [show i + (n - s) = i + 1 + (n - 1 - s) by omega]
      _ = ∑ s ∈ Finset.range n, ω (-x (i + 1 + s)) :=
          Finset.sum_range_reflect (fun s => ω (-x (i + 1 + s))) n

private theorem dev_next (u : Lattice) (q : ℝ) (V : Set Lattice) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (s : ℕ) :
    |GreedyAttachment.deviation u q (s + 1) (GreedyAttachment.vertex u q V (s + 1))| ≤
      |GreedyAttachment.deviation u q s (GreedyAttachment.vertex u q V s)| + 1 := by
  rw [GreedyAttachment.deviation_step]
  have h1 := neg_abs_le (GreedyAttachment.deviation u q s (GreedyAttachment.vertex u q V s))
  have h2 := le_abs_self (GreedyAttachment.deviation u q s (GreedyAttachment.vertex u q V s))
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith
private theorem r_sub (a : ℝ) (u x : Lattice) (s : ℕ) (hl : x.1 + x.2 = u.1 + u.2 + (s : ℤ)) :
    (1 - a) * (x.1 : ℝ) - a * (x.2 : ℝ) - ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)) =
      GreedyAttachment.deviation u a s x := by
  have h := GreedyAttachment.transverse_deviation_eq u x a a s hl
  linarith
private theorem r_neg (a : ℝ) (u x : Lattice) :
    (1 - a) * ((-x).1 : ℝ) - a * ((-x).2 : ℝ) - ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)) =
      -((1 - a) * (x.1 : ℝ) - a * (x.2 : ℝ) -
        ((1 - a) * ((-u).1 : ℝ) - a * ((-u).2 : ℝ))) := by
  simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  ring
private theorem lev_neg (y : Lattice) :
    (((-y).1 + (-y).2 : ℤ) : ℝ) = -((y.1 + y.2 : ℤ) : ℝ) := by
  rw [show (-y).1 + (-y).2 = -(y.1 + y.2) by simp only [Prod.fst_neg, Prod.snd_neg]; ring,
    Int.cast_neg]
private theorem mem_Qk (a A R C₁ M Pk W0 : ℝ) (y u : Lattice)
    (hl : |((y.1 + y.2 : ℤ) : ℝ)| ≤ (A + 5) * M)
    (hr : |(1 - a) * (y.1 : ℝ) - a * (y.2 : ℝ) - ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤ W0 + 1)
    (hu : |(1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)| ≤ R * Pk) (hW : W0 + 1 ≤ Pk) (hC : 0 ≤ C₁) :
    |((y.1 + y.2 : ℤ) : ℝ)| ≤ (A + 5) * M ∧
      |(1 - a) * (y.1 : ℝ) - a * (y.2 : ℝ)| ≤ (R + 2 * C₁ + 10) * Pk := by
  refine ⟨hl, ?_⟩
  have hPk : 0 ≤ Pk := (abs_nonneg _).trans (hr.trans hW)
  have h3 : 0 ≤ C₁ * Pk := mul_nonneg hC hPk
  rw [show (R + 2 * C₁ + 10) * Pk = R * Pk + 2 * (C₁ * Pk) + 10 * Pk by ring, abs_le]
  rw [abs_le] at hr hu
  constructor <;> linarith [hr.1, hr.2, hu.1, hu.2]

/-- The induction closing the circle, in the frame of a greedy sequence `X = vertex u' a V`. -/
private theorem frame (Qs : Set Lattice) (w : Lattice → ℝ) (a T Cm t A M W0 : ℝ) (u' : Lattice)
    (V : Set Lattice) (off i l : ℕ) (ha0 : 0 < a) (ha1 : a < 1) (hu0 : u' ∈ Qs)
    (hQs : ∀ y : Lattice, |((y.1 + y.2 : ℤ) : ℝ)| ≤ (A + 5) * M →
      |(1 - a) * (y.1 : ℝ) - a * (y.2 : ℝ) - ((1 - a) * (u'.1 : ℝ) - a * (u'.2 : ℝ))| ≤ W0 + 1 →
      y ∈ Qs)
    (hlo : -((A + 5) * M) ≤ ((u'.1 + u'.2 : ℤ) : ℝ))
    (hhi : ((u'.1 + u'.2 : ℤ) : ℝ) + ((i + l : ℕ) : ℝ) ≤ (A + 5) * M)
    (hS : ∀ n, (∀ r ≤ n, GreedyAttachment.vertex u' a V r ∈ Qs) → ∀ r ≤ n,
      -T ≤ w (GreedyAttachment.vertex u' a V r) ∧
        |GreedyAttachment.deviation u' a r (GreedyAttachment.vertex u' a V r)| ≤ W0)
    (hE : (∀ s, s ≤ i + l → GreedyAttachment.vertex u' a V s ∈ Qs) →
      (∀ s, s < l → -T ≤ w (GreedyAttachment.vertex u' a V (i + off + s))) →
      -2 * Cm * (l : ℝ) - t / 2 ≤
        ∑ s ∈ Finset.range l, w (GreedyAttachment.vertex u' a V (i + off + s)))
    (hoff : off ≤ 1) :
    (∀ r ≤ i + l, |(1 - a) * ((GreedyAttachment.vertex u' a V r).1 : ℝ) -
        a * ((GreedyAttachment.vertex u' a V r).2 : ℝ) -
        ((1 - a) * (u'.1 : ℝ) - a * (u'.2 : ℝ))| ≤ W0) ∧
      -2 * Cm * (l : ℝ) - t / 2 ≤
        ∑ s ∈ Finset.range l, w (GreedyAttachment.vertex u' a V (i + off + s)) := by
  have key : ∀ s, s ≤ i + l → ∀ r ≤ s, GreedyAttachment.vertex u' a V r ∈ Qs := by
    intro s
    induction s with
    | zero =>
      intro _ r hr
      obtain rfl : r = 0 := by omega
      exact hu0
    | succ s ih =>
      intro hs r hr
      rcases Nat.lt_or_ge r (s + 1) with h | h
      · exact ih (by omega) r (by omega)
      · obtain rfl : r = s + 1 := by omega
        have hds := (hS s (ih (by omega)) s le_rfl).2
        have hd := dev_next u' a V ha0.le ha1.le s
        have hlev := GreedyAttachment.level u' a V (s + 1)
        have hcast : (((GreedyAttachment.vertex u' a V (s + 1)).1 +
            (GreedyAttachment.vertex u' a V (s + 1)).2 : ℤ) : ℝ) =
            ((u'.1 + u'.2 : ℤ) : ℝ) + ((s + 1 : ℕ) : ℝ) := by exact_mod_cast hlev
        apply hQs
        · rw [abs_le, hcast]
          constructor <;> linarith [(Nat.cast_nonneg (s + 1) : (0 : ℝ) ≤ ((s + 1 : ℕ) : ℝ)),
            (by exact_mod_cast hs : ((s + 1 : ℕ) : ℝ) ≤ ((i + l : ℕ) : ℝ))]
        · rw [r_sub a u' _ (s + 1) hlev]
          linarith
  have hall : ∀ r ≤ i + l, GreedyAttachment.vertex u' a V r ∈ Qs := fun r hr =>
    key (i + l) le_rfl r hr
  have hfull := hS (i + l) hall
  exact ⟨fun r hr => by
      rw [r_sub a u' _ r (GreedyAttachment.level u' a V r)]
      exact (hfull r hr).2,
    hE (fun s hs => hall s hs) (fun s hs => (hfull (i + off + s) (by omega)).1)⟩

/-- The arithmetic of (B.10) and (5.29) of the differentiability preprint. -/
private theorem fine_piece (ω : Environment) (a G0 dl dr K Cm cstar C₁ t P W0 ρ : ℝ) (l : ℕ)
    (z₀ : Lattice) (D : ℕ × ℕ) (y : Path z₀ D) (hDl : D.1 + D.2 = l)
    (hy : ∀ v, |(1 - a) * ((y.vertex v).1 : ℝ) - a * ((y.vertex v).2 : ℝ) - ρ| ≤ W0)
    (hW : -2 * Cm * (l : ℝ) - t / 2 ≤ pathWeight ω y)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hdl : |dl| ≤ K) (hdr : |dr| ≤ K) (hG : 0 ≤ G0 + 2 * Cm)
    (hC : 8 * cstar * (G0 + 2 * Cm) + 1 ≤ C₁) (hC1 : 1 ≤ C₁) (hW0 : 0 ≤ W0)
    (hP : 2 * W0 * K ≤ P) (hl : (l : ℝ) < 8 * cstar * P) :
    G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
        pathWeight ω y ≤ C₁ * P + 2 * t ∧
    G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
        pathWeight ω y ≤ C₁ * P + 2 * t ∧
    ∀ v, |(1 - a) * ((y.vertex v).1 : ℝ) - a * ((y.vertex v).2 : ℝ) - ρ| ≤ C₁ * P := by
  have h0 := hy 0
  have h1 := hy (Fin.last (D.1 + D.2))
  rw [y.start] at h0
  rw [y.finish] at h1
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_natCast] at h1
  have hrD : |(1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)| ≤ 2 * W0 := by
    rw [abs_le] at h0 h1 ⊢
    constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
  have key : ∀ s r : ℝ, |s| ≤ K → |r| ≤ 2 * W0 → s * r ≤ P := fun s r hs hr =>
    calc s * r ≤ |s * r| := le_abs_self _
      _ = |s| * |r| := abs_mul s r
      _ ≤ K * (2 * W0) := mul_le_mul hs hr (abs_nonneg r) ((abs_nonneg s).trans hs)
      _ = 2 * W0 * K := by ring
      _ ≤ P := hP
  have hWK : 0 ≤ W0 * K := mul_nonneg hW0 (by linarith)
  have hP0 : 0 ≤ P := by linarith
  have hmul := mul_le_mul_of_nonneg_left hl.le hG
  have hc : (8 * cstar * (G0 + 2 * Cm)) * P ≤ (C₁ - 1) * P :=
    mul_le_mul_of_nonneg_right (by linarith) hP0
  have e : (G0 + 2 * Cm) * (8 * cstar * P) = (8 * cstar * (G0 + 2 * Cm)) * P := by ring
  have hWP : W0 ≤ P := by linarith [mul_le_mul_of_nonneg_left hK hW0]
  have hlR : (D.1 : ℝ) + (D.2 : ℝ) = l := by exact_mod_cast hDl
  refine ⟨?_, ?_, fun v => (hy v).trans (hWP.trans (le_mul_of_one_le_left hP0 hC1))⟩
  · have := key dl _ hdl hrD
    rw [hlR]
    linarith
  · have := key dr _ hdr hrD
    rw [hlR]
    linarith

/-- **The fine piece of Lemma 5.7 (i) along `γ^u`, general weights.** -/
theorem grid_fine_general
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
  0 ≤ t → 0 ≤ cstar → 1 ≤ K → |dl| ≤ K → |dr| ≤ K → 0 ≤ G0 + 2 * Cm →
  8 * cstar * (G0 + 2 * Cm) + 1 ≤ C₁ →
  ⌈((m k : ℝ) - 1) / 4⌉₊ ≤ k →
  2 * (W0 : ℝ) * K ≤ ((2 ^ (k - ⌈((m k : ℝ) - 1) / 4⌉₊) : ℕ) : ℝ) →
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
  ∀ u : Lattice, |((u.1 + u.2 : ℤ) : ℝ)| ≤ A * 2 ^ m k →
    |(1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)| ≤ R * 2 ^ k →
    ∀ j : ℕ, J ≤ j → j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
    ((2 ^ (m k - 4 * j - 1) : ℕ) : ℝ) < 8 * cstar * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) →
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
  intro θ₁ _ _ Ntr W0 _ _ _ _ _ _ Egeo Qk Nl Vb Wb _ _ ha0 ha1 hm1 hK1 hJ ht hcs hK hdl hdr hG hC
    hjk hWK hEg hE1 hE2 u hu1 hu2 j hJj hjj hfine I _ hI
  have hM0 : (0 : ℝ) < (2 : ℝ) ^ (m k) := by positivity
  have hW0 : (1 : ℝ) ≤ (W0 : ℝ) := Nat.one_le_cast.mpr (by show 1 ≤ Ntr + 1; omega)
  have hC1 : 1 ≤ C₁ := by
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hcs) hG
    linarith
  set jst : ℕ := ⌈((m k : ℝ) - 1) / 4⌉₊
  have hWKj : 2 * (W0 : ℝ) * K ≤ (j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ) := by
    have h1 : ((2 ^ (k - jst) : ℕ) : ℝ) ≤ ((2 ^ (k - j) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hJ.trans hJj)
    have h3 := mul_nonneg (sub_nonneg.mpr h2)
      (Nat.cast_nonneg _ : (0 : ℝ) ≤ ((2 ^ (k - j) : ℕ) : ℝ))
    linarith
  have hW1 : (W0 : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
    have h2k : ((2 ^ (k - jst) : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := by
      exact_mod_cast pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le k jst)
    nlinarith [mul_le_mul_of_nonneg_left hK (by linarith : (0 : ℝ) ≤ W0)]
  have hlM : ((2 ^ (m k - 4 * j - 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m k) := by
    exact_mod_cast pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : m k - 4 * j - 1 ≤ m k)
  have hlNl : ((2 ^ (m k - 4 * j - 1) : ℕ) : ℝ) ≤ Nl := by
    have h1 : (j : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg j) (by exact_mod_cast hjj.trans hjk) 2
    have h2 : ((2 ^ (k - j) : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := by
      exact_mod_cast pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le k j)
    have h3 := mul_le_mul h1 h2 (Nat.cast_nonneg _) (sq_nonneg (k : ℝ))
    show _ ≤ 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k
    linarith [mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 8 * cstar)]
  have hθ : θ₁ = min a (1 - a) / 5 := rfl
  have hmn : 0 < min a (1 - a) := lt_min ha0 (by linarith)
  have hmin := min_le_left a (1 - a)
  have hmin' := min_le_right a (1 - a)
  obtain ⟨hIlo, hIhi⟩ := abs_le.mp hI
  obtain ⟨hulo, huhi⟩ := abs_le.mp hu1
  have hu_mem : u ∈ Qk :=
    mem_Qk a A R C₁ ((2 : ℝ) ^ (m k)) ((2 : ℝ) ^ k) (W0 : ℝ) u u
      (abs_le.mpr ⟨by linarith, by linarith⟩) (by simp only [sub_self, abs_zero]; linarith)
      hu2 hW1 (by linarith)
  obtain ⟨l, hl⟩ : ∃ l : ℕ, 2 ^ (m k - 4 * j - 1) = l := ⟨_, rfl⟩
  rw [hl] at hfine hlM hlNl ⊢
  set P : ℝ := (j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)
  refine ⟨fun hu3 _ hI3 z₀ z₁ hz₀ hz₁ => ?_, fun hnt hIu _ z₀ z₁ hz₀ hz₁ => ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = u.1 + u.2 - (I + l) :=
      ⟨_, Int.toNat_of_nonneg (by omega)⟩
    have hi' : (i : ℝ) = ((u.1 + u.2 : ℤ) : ℝ) - ((I : ℝ) + (l : ℝ)) := by exact_mod_cast hi
    have hS := stair_greedy_backward ω T θ₁ m1 K1 Qk (by linarith) (by linarith) hm1 hK1 hEg u
      hu_mem hu3.1 hu3.2 a (by linarith) (by linarith)
    obtain ⟨hloc, hw⟩ := frame {y | -y ∈ Qk} (fun y => ω (-y)) a T Cm t A ((2 : ℝ) ^ (m k))
      (W0 : ℝ) (-u) Wb 1 i l ha0 ha1 (by show -(-u) ∈ Qk; rw [neg_neg]; exact hu_mem)
      (fun y h1 h2 => mem_Qk a A R C₁ ((2 : ℝ) ^ (m k)) ((2 : ℝ) ^ k) (W0 : ℝ) (-y) u
        (by rw [lev_neg, abs_neg]; exact h1)
        (by rw [r_neg, abs_neg]; exact h2) hu2 hW1 (by linarith))
      (by rw [lev_neg]; linarith)
      (by rw [lev_neg]; linarith [(Nat.cast_add i l : ((i + l : ℕ) : ℝ) = (i : ℝ) + (l : ℝ))])
      (fun n hq r hr => ⟨(hS n hq r hr).1, (hS n hq r hr).2.2⟩) (hE2 u i l hlNl) le_rfl
    have e0 : (u.1 + u.2 - I).toNat = i + l := by omega
    have e1 : (u.1 + u.2 - (I + (l : ℤ))).toNat = i := by omega
    obtain ⟨D, q, hDl, hD, hv, hqw⟩ := seq_path_rev ω (GreedyAttachment.vertex (-u) a Wb)
      (fun s => GreedyAttachment.step (-u) a Wb s) i l z₀ z₁ (by rw [hz₀, e0]; try rfl)
      (by rw [hz₁, e1]; try rfl)
    exact ⟨D, q, hD, fine_piece ω a G0 dl dr K Cm cstar C₁ t P (W0 : ℝ)
      ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)) l z₀ D q hDl
      (fun v => by rw [hv v, r_neg, abs_neg]; exact hloc _ (by have := v.isLt; omega))
      (by rw [hqw]; exact hw) ht hK hdl hdr hG hC hC1 (by linarith) hWKj hfine⟩
  · obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = I - (u.1 + u.2) := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    have hi' : (i : ℝ) = (I : ℝ) - ((u.1 + u.2 : ℤ) : ℝ) := by exact_mod_cast hi
    have hS := stair_greedy_forward ω T θ₁ m1 K1 Qk (by linarith) (by linarith) hm1 hK1 hEg u
      hu_mem hnt a (by linarith) (by linarith)
    obtain ⟨hloc, hw⟩ := frame Qk ω a T Cm t A ((2 : ℝ) ^ (m k)) (W0 : ℝ) u Vb 0 i l ha0 ha1
      hu_mem (fun y h1 h2 => mem_Qk a A R C₁ ((2 : ℝ) ^ (m k)) ((2 : ℝ) ^ k) (W0 : ℝ) y u h1 h2
        hu2 hW1 (by linarith))
      (by linarith)
      (by linarith [hlM, (Nat.cast_add i l : ((i + l : ℕ) : ℝ) = (i : ℝ) + (l : ℝ))])
      (fun n hq r hr => ⟨(hS n hq r hr).2.1, (hS n hq r hr).2.2⟩) (hE1 u i l hlNl) (by omega)
    have e0 : (I - (u.1 + u.2)).toNat = i := by omega
    have e1 : (I + (l : ℤ) - (u.1 + u.2)).toNat = i + l := by omega
    obtain ⟨D, p, hDl, hD, hv, hpw⟩ := seq_path ω (GreedyAttachment.vertex u a Vb)
      (fun s => GreedyAttachment.step u a Vb s) i l z₀ z₁ (by rw [hz₀, e0]; try rfl)
      (by rw [hz₁, e1]; try rfl)
    exact ⟨D, p, hD, fine_piece ω a G0 dl dr K Cm cstar C₁ t P (W0 : ℝ)
      ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)) l z₀ D p hDl
      (fun v => by rw [hv v]; exact hloc _ (by have := v.isLt; omega))
      (by rw [hpw]; exact hw) ht hK hdl hdr hG hC hC1 (by linarith) hWKj hfine⟩

end LPPDifferentiability
