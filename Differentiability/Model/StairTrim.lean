/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Environment
public import LPP_Foundations.Frozen.Model.Path
public import Differentiability.Model.StairTrappedComponents
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Interval

/-! # Trimming the ends of a path

Item (v) of Lemma B.5 of the differentiability preprint, with the box distance `2L`
(`c₀ = W₀ + 2L + 1`). On the event `Egeo`, among any `r₀ + 1` consecutive vertices of an
admissible path whose vertices lie in `Q` there is one whose box `v - [0, L]²` has no very bad
site, one that is not trapped, and one outside `V ∪ V̄←`.

The argument follows the differentiability preprint. If every one of the `r₀ + 1` vertices had a
very bad site in its box, choose one for each vertex. A path meets a box `y + [0, L]²` in at most
`2L + 1` vertices, because the level of the vertices grows by one at each step, so there are more
than `K₁` different very bad sites. All of them are within `r₀ + 2L` of each other and lie in the
collar `𝒬⁺⁺`, which the cluster clause of `Egeo` forbids. The other two claims follow from the
bound on trapped components, applied to the first `Ntr + 1` vertices.
-/

public section

namespace LPPDifferentiability

/-- Vertex `n` of a path, with the start as a harmless default beyond the end. -/
private def pv {u : Lattice} {d : ℕ × ℕ} (p : Path u d) (n : ℕ) : Lattice :=
  if h : n < d.1 + d.2 + 1 then p.vertex ⟨n, h⟩ else u

private theorem pv_of_lt {u : Lattice} {d : ℕ × ℕ} (p : Path u d) {n : ℕ}
    (h : n < d.1 + d.2 + 1) : pv p n = p.vertex ⟨n, h⟩ := by
  simp [pv, h]

private theorem pv_zero {u : Lattice} {d : ℕ × ℕ} (p : Path u d) : pv p 0 = u := by
  have h0 : (⟨0, Nat.succ_pos _⟩ : Fin (d.1 + d.2 + 1)) = 0 := Fin.ext (by simp)
  rw [pv_of_lt p (Nat.succ_pos _)]
  exact (congrArg p.vertex h0).trans p.start

private theorem pv_succ {u : Lattice} {d : ℕ × ℕ} (p : Path u d) {n : ℕ} (h : n < d.1 + d.2) :
    pv p (n + 1) = pv p n + (1, 0) ∨ pv p (n + 1) = pv p n + (0, 1) := by
  rw [pv_of_lt p (by omega : n + 1 < d.1 + d.2 + 1), pv_of_lt p (by omega : n < d.1 + d.2 + 1)]
  exact p.step ⟨n, h⟩

private theorem pv_step {u : Lattice} {d : ℕ × ℕ} (p : Path u d) {n : ℕ} (h : n < d.1 + d.2) :
    (pv p n).1 ≤ (pv p (n + 1)).1 ∧ (pv p n).2 ≤ (pv p (n + 1)).2 ∧
      (pv p (n + 1)).1 + (pv p (n + 1)).2 = (pv p n).1 + (pv p n).2 + 1 := by
  rcases pv_succ p h with e | e <;> rw [e] <;> simp only [Prod.fst_add, Prod.snd_add] <;>
    refine ⟨?_, ?_, ?_⟩ <;> omega

private theorem pv_between_aux {u : Lattice} {d : ℕ × ℕ} (p : Path u d) (m : ℕ) :
    ∀ k : ℕ, m + k ≤ d.1 + d.2 →
      (pv p m).1 ≤ (pv p (m + k)).1 ∧ (pv p m).2 ≤ (pv p (m + k)).2 ∧
      (pv p (m + k)).1 + (pv p (m + k)).2 = (pv p m).1 + (pv p m).2 + (k : ℤ) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro h
    obtain ⟨a1, a2, a3⟩ := ih (by omega)
    obtain ⟨b1, b2, b3⟩ := pv_step p (n := m + k) (by omega)
    rw [← Nat.add_assoc]
    refine ⟨by omega, by omega, ?_⟩
    push_cast
    omega

/-- Along a path the coordinates do not decrease and the level grows by one per step. -/
private theorem pv_between {u : Lattice} {d : ℕ × ℕ} (p : Path u d) {m n : ℕ} (hmn : m ≤ n)
    (hn : n ≤ d.1 + d.2) :
    (pv p m).1 ≤ (pv p n).1 ∧ (pv p m).2 ≤ (pv p n).2 ∧
      (pv p n).1 + (pv p n).2 = (pv p m).1 + (pv p m).2 + ((n : ℤ) - (m : ℤ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨a1, a2, a3⟩ := pv_between_aux p m k hn
  exact ⟨a1, a2, by omega⟩

private theorem pv_level {u : Lattice} {d : ℕ × ℕ} (p : Path u d) {n : ℕ} (hn : n ≤ d.1 + d.2) :
    (pv p n).1 + (pv p n).2 = u.1 + u.2 + (n : ℤ) := by
  obtain ⟨_, _, h⟩ := pv_between p (Nat.zero_le n) hn
  rw [pv_zero] at h
  omega

private theorem pv_inj {u : Lattice} {d : ℕ × ℕ} (p : Path u d) {m n : ℕ} (hm : m ≤ d.1 + d.2)
    (hn : n ≤ d.1 + d.2) (h : pv p m = pv p n) : m = n := by
  have h1 := pv_level p hm
  have h2 := pv_level p hn
  rw [h] at h1
  omega

private theorem exists_fin {u : Lattice} {d : ℕ × ℕ} (p : Path u d) (s r0 : ℕ)
    (hs : s + r0 ≤ d.1 + d.2) (P : Lattice → Prop)
    (h : ∃ n, s ≤ n ∧ n ≤ s + r0 ∧ P (pv p n)) :
    ∃ i : Fin (d.1 + d.2 + 1), s ≤ i.val ∧ i.val ≤ s + r0 ∧ P (p.vertex i) := by
  obtain ⟨n, h1, h2, h3⟩ := h
  have hn : n < d.1 + d.2 + 1 := by omega
  refine ⟨⟨n, hn⟩, h1, h2, ?_⟩
  rwa [pv_of_lt p hn] at h3

private theorem l1_le_of (a b : Lattice) (B : ℤ) (h1 : a.1 - b.1 + (a.2 - b.2) ≤ B)
    (h2 : a.1 - b.1 - (a.2 - b.2) ≤ B) (h3 : b.1 - a.1 + (b.2 - a.2) ≤ B)
    (h4 : b.1 - a.1 - (b.2 - a.2) ≤ B) : |a.1 - b.1| + |a.2 - b.2| ≤ B := by
  rcases abs_cases (a.1 - b.1) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
    rcases abs_cases (a.2 - b.2) with ⟨e2, _⟩ | ⟨e2, _⟩ <;> omega

private theorem exists_bad_in_box (ω : Environment) (T : ℝ) (L : ℕ) (v : Lattice)
    (h : ¬ ∀ y : Lattice, v.1 - (L : ℤ) ≤ y.1 → y.1 ≤ v.1 → v.2 - (L : ℤ) ≤ y.2 → y.2 ≤ v.2 →
      -T ≤ ω y) :
    ∃ y : Lattice, v.1 - (L : ℤ) ≤ y.1 ∧ y.1 ≤ v.1 ∧ v.2 - (L : ℤ) ≤ y.2 ∧ y.2 ≤ v.2 ∧
      ω y < -T := by
  by_contra hy
  apply h
  intro y h1 h2 h3 h4
  by_contra hω
  exact hy ⟨y, h1, h2, h3, h4, not_le.mp hω⟩

private theorem exists_inj_into (S : Finset Lattice) (n : ℕ) (h : n ≤ S.card) :
    ∃ f : Fin n → Lattice, Function.Injective f ∧ ∀ i, f i ∈ S := by
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq h
  let e : t ≃ Fin n := Finset.equivFinOfCardEq htc
  exact ⟨fun i => (e.symm i).1, fun a b hab => e.symm.injective (Subtype.ext hab),
    fun i => hts (e.symm i).2⟩

/-- Consecutive vertices of a path, all in `Q`, form a chain: used to apply the bound on trapped
components to the first `N + 1` vertices. -/
private theorem no_chain_on_path {u : Lattice} {d : ℕ × ℕ} (p : Path u d) (s N : ℕ)
    (hs : s + N ≤ d.1 + d.2) (Q : Set Lattice) (c D1 : ℕ) (hD : 1 ≤ D1)
    (hQ : ∀ n, s ≤ n → n ≤ s + N → pv p n ∈ Q) (P : Lattice → Prop)
    (hP : ∀ n, s ≤ n → n ≤ s + N → P (pv p n))
    (hno : ¬ ∃ f : Fin (N + 1) → Lattice, Function.Injective f ∧
        (∀ i, f i ∈ {z : Lattice | ∃ y ∈ Q, |z.1 - y.1| + |z.2 - y.2| ≤ (c : ℤ)} ∧ P (f i)) ∧
        ∀ i : Fin (N + 1), 0 < i.val → ∃ j : Fin (N + 1), j.val < i.val ∧
          |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ (D1 : ℤ)) : False := by
  apply hno
  refine ⟨fun i => pv p (s + i.val), ?_, ?_, ?_⟩
  · intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    have := pv_inj p (by omega : s + a.val ≤ d.1 + d.2) (by omega : s + b.val ≤ d.1 + d.2) hab
    exact Fin.ext (by omega)
  · intro i
    have hi := i.isLt
    refine ⟨⟨pv p (s + i.val), hQ _ (by omega) (by omega), ?_⟩, hP _ (by omega) (by omega)⟩
    simp
  · intro i hi
    have hi' := i.isLt
    refine ⟨⟨i.val - 1, by omega⟩, by show i.val - 1 < i.val; omega, ?_⟩
    obtain ⟨x1, x2, x3⟩ :=
      pv_between p (m := s + (i.val - 1)) (n := s + i.val) (by omega) (by omega)
    show |(pv p (s + i.val)).1 - (pv p (s + (i.val - 1))).1| +
      |(pv p (s + i.val)).2 - (pv p (s + (i.val - 1))).2| ≤ (D1 : ℤ)
    apply l1_le_of <;> omega

/-- **Trimming** (item (v) of Lemma B.5): on the event `Egeo`, among any `r0 + 1` consecutive
vertices of an admissible path with vertices in `Q` there is one whose box `v - [0, L]²` has no
very bad site, one that is not trapped, and one outside `V ∪ V̄←`. -/
theorem stair_trim (ω : Environment) (T θ₁ : ℝ) (m1 K1 : ℕ) (Q : Set Lattice) :
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
  ∀ (u : Lattice) (d : ℕ × ℕ) (p : Path u d) (s : ℕ), s + r0 ≤ d.1 + d.2 →
    (∀ i : Fin (d.1 + d.2 + 1), s ≤ i.val → i.val ≤ s + r0 → p.vertex i ∈ Q) →
    (∃ i : Fin (d.1 + d.2 + 1), s ≤ i.val ∧ i.val ≤ s + r0 ∧ boxFree ω T (p.vertex i)) ∧
    (∃ i : Fin (d.1 + d.2 + 1), s ≤ i.val ∧ i.val ≤ s + r0 ∧
      ¬ (reach ω T (p.vertex i)).Finite) ∧
    (∃ i : Fin (d.1 + d.2 + 1), s ≤ i.val ∧ i.val ≤ s + r0 ∧
      -T ≤ ω (p.vertex i) ∧ ¬ (reachBack ω T (p.vertex i)).Finite) := by
  intro reach reachBack Ntr W0 L r0 D1 d0 c0 collar Egeo boxFree hθ hθ' hm hK hE u d p s hs hQ
  have hr0 : r0 = K1 * (2 * L + 1) + Ntr := rfl
  have hD1 : D1 = ⌊2 * (W0 : ℝ) / θ₁⌋₊ + 4 * W0 + 2 * r0 + 2 * L + 8 := rfl
  have hd0 : d0 = D1 + 2 * m1 ^ 2 := rfl
  have hc0 : c0 = W0 + 2 * L + 1 := rfl
  have hNr : Ntr ≤ r0 := by omega
  have hQ' : ∀ n, s ≤ n → n ≤ s + r0 → pv p n ∈ Q := by
    intro n h1 h2
    have hn : n < d.1 + d.2 + 1 := by omega
    rw [pv_of_lt p hn]
    exact hQ ⟨n, hn⟩ h1 h2
  have hS := stair_trapped_components_le ω T θ₁ m1 K1 Q hθ hθ' hm hK hE
  obtain ⟨hcl, -⟩ := hE
  refine ⟨exists_fin p s r0 hs (boxFree ω T) ?_,
    exists_fin p s r0 hs (fun v => ¬ (reach ω T v).Finite) ?_,
    exists_fin p s r0 hs (fun v => -T ≤ ω v ∧ ¬ (reachBack ω T v).Finite) ?_⟩
  · -- The boxes.
    by_contra hno
    have hno' : ∀ n, s ≤ n → n ≤ s + r0 → ¬ boxFree ω T (pv p n) :=
      fun n h1 h2 hb => hno ⟨n, h1, h2, hb⟩
    have hb : ∀ n : Fin (r0 + 1), ∃ y : Lattice,
        (pv p (s + n.val)).1 - (L : ℤ) ≤ y.1 ∧ y.1 ≤ (pv p (s + n.val)).1 ∧
        (pv p (s + n.val)).2 - (L : ℤ) ≤ y.2 ∧ y.2 ≤ (pv p (s + n.val)).2 ∧ ω y < -T := by
      intro n
      have hn := n.isLt
      exact exists_bad_in_box ω T L (pv p (s + n.val)) (hno' (s + n.val) (by omega) (by omega))
    choose g hg1 hg2 hg3 hg4 hg5 using hb
    have hfiber : ∀ b ∈ Finset.univ.image g,
        (Finset.univ.filter (fun a : Fin (r0 + 1) => g a = b)).card ≤ 2 * L + 1 := by
      intro b _
      have hle : (Finset.univ.filter (fun a : Fin (r0 + 1) => g a = b)).card ≤
          (Finset.Icc (b.1 + b.2 - (u.1 + u.2) - (s : ℤ))
            (b.1 + b.2 - (u.1 + u.2) - (s : ℤ) + 2 * (L : ℤ))).card := by
        apply Finset.card_le_card_of_injOn (fun a : Fin (r0 + 1) => (a.val : ℤ))
        · intro a ha
          have hga : g a = b := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
          have ha' := a.isLt
          have e1 := hg1 a
          have e2 := hg2 a
          have e3 := hg3 a
          have e4 := hg4 a
          rw [hga] at e1 e2 e3 e4
          have lv := pv_level p (n := s + a.val) (by omega)
          show (a.val : ℤ) ∈ Finset.Icc _ _
          rw [Finset.mem_Icc]
          push_cast at lv
          omega
        · intro a _ b' _ hab
          have hab' : (a.val : ℤ) = b'.val := hab
          exact Fin.ext (by omega)
      rw [Int.card_Icc] at hle
      omega
    have hcard : (Finset.univ : Finset (Fin (r0 + 1))).card ≤
        (2 * L + 1) * (Finset.univ.image g).card :=
      Finset.card_le_mul_card_image Finset.univ (2 * L + 1) hfiber
    have hSc : K1 + 1 ≤ (Finset.univ.image g).card := by
      by_contra hlt
      have h1 : (2 * L + 1) * (Finset.univ.image g).card ≤ (2 * L + 1) * K1 :=
        Nat.mul_le_mul_left _ (by omega)
      have h2 : (Finset.univ : Finset (Fin (r0 + 1))).card = r0 + 1 := by simp
      have h3 : (2 * L + 1) * K1 = K1 * (2 * L + 1) := Nat.mul_comm _ _
      omega
    obtain ⟨f, hfinj, hfS⟩ := exists_inj_into (Finset.univ.image g) (K1 + 1) hSc
    have hcc : 2 * (L : ℤ) ≤ ((c0 + m1 ^ 2 : ℕ) : ℤ) := by
      have : 2 * L ≤ c0 + m1 ^ 2 := by omega
      exact_mod_cast this
    have hgcol : ∀ a : Fin (r0 + 1), ∃ y ∈ Q,
        |(g a).1 - y.1| + |(g a).2 - y.2| ≤ ((c0 + m1 ^ 2 : ℕ) : ℤ) := by
      intro a
      have ha := a.isLt
      have e1 := hg1 a
      have e2 := hg2 a
      have e3 := hg3 a
      have e4 := hg4 a
      refine ⟨pv p (s + a.val), hQ' _ (by omega) (by omega), ?_⟩
      apply l1_le_of <;> omega
    have hgdist : ∀ a b : Fin (r0 + 1),
        |(g a).1 - (g b).1| + |(g a).2 - (g b).2| ≤ (d0 : ℤ) := by
      intro a b
      have ha := a.isLt
      have hb := b.isLt
      have e1 := hg1 a
      have e2 := hg2 a
      have e3 := hg3 a
      have e4 := hg4 a
      have f1 := hg1 b
      have f2 := hg2 b
      have f3 := hg3 b
      have f4 := hg4 b
      have hdd : (r0 : ℤ) + 2 * L ≤ d0 := by
        have : r0 + 2 * L ≤ d0 := by omega
        exact_mod_cast this
      rcases le_total a.val b.val with hab | hab
      · obtain ⟨x1, x2, x3⟩ :=
          pv_between p (m := s + a.val) (n := s + b.val) (by omega) (by omega)
        apply l1_le_of <;> omega
      · obtain ⟨x1, x2, x3⟩ :=
          pv_between p (m := s + b.val) (n := s + a.val) (by omega) (by omega)
        apply l1_le_of <;> omega
    have hfmem : ∀ i : Fin (K1 + 1), f i ∈ collar Q (c0 + m1 ^ 2) ∧ ω (f i) < -T := by
      intro i
      obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (hfS i)
      rw [← ha]
      exact ⟨hgcol a, hg5 a⟩
    have hfchain : ∀ i : Fin (K1 + 1), 0 < i.val → ∃ j : Fin (K1 + 1), j.val < i.val ∧
        |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ (d0 : ℤ) := by
      intro i hi
      refine ⟨⟨0, by omega⟩, hi, ?_⟩
      obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (hfS i)
      obtain ⟨b, -, hb⟩ := Finset.mem_image.mp (hfS ⟨0, by omega⟩)
      rw [← ha, ← hb]
      exact hgdist a b
    exact hcl ⟨f, hfinj, hfmem, hfchain⟩
  · -- Not trapped.
    by_contra hno
    have hno' : ∀ n, s ≤ n → n ≤ s + r0 → (reach ω T (pv p n)).Finite := by
      intro n h1 h2
      by_contra hf
      exact hno ⟨n, h1, h2, hf⟩
    exact no_chain_on_path p s Ntr (by omega) Q c0 D1 (by omega)
      (fun n h1 h2 => hQ' n h1 (by omega))
      (fun v => (reach ω T v).Finite) (fun n h1 h2 => hno' n h1 (by omega)) hS.1
  · -- Outside `V ∪ V̄←`.
    by_contra hno
    have hno' : ∀ n, s ≤ n → n ≤ s + r0 →
        (ω (pv p n) < -T ∨ (reachBack ω T (pv p n)).Finite) := by
      intro n h1 h2
      by_cases hω : -T ≤ ω (pv p n)
      · right
        by_contra hf
        exact hno ⟨n, h1, h2, hω, hf⟩
      · left
        exact not_le.mp hω
    exact no_chain_on_path p s Ntr (by omega) Q c0 D1 (by omega)
      (fun n h1 h2 => hQ' n h1 (by omega))
      (fun v => ω v < -T ∨ (reachBack ω T v).Finite) (fun n h1 h2 => hno' n h1 (by omega)) hS.2

end LPPDifferentiability
