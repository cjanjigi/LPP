/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.PathWeight
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # Staircase families of one grid interval and one bin

Deterministic counting for the grid lemma: the fine count (5.15) and the staircase
count (5.25) of the differentiability preprint.

* `fine_staircase_representatives`: for fixed `I`, `l`, `w` and bin `[h w, (h + 1) w)`, as `ρ`
  ranges over the bin the integer parts `⌊ρ + a (I + i)⌋`, `0 ≤ i ≤ l`, that give the staircase
  of `ρ` take at most `(l + 1) w + 1` different value lists. Concretely, there is a set of at most
  `(l + 1) w + 1` values of `ρ` in the bin such that every `ρ` of the bin has all of these integer
  parts equal to those of one of them.
* `path_weight_eq_sum_of_vertex_formula`: a path whose vertices are given by a formula has weight
  the sum of the environment over the formula.
* `coarse_attachment_family`: the pairs (start, displacement) of the two attachment staircases at
  a coarse scale lie in a set of at most `2 (w + 1) j² (16 w + 2)` pairs.
-/

public section

namespace LPPDifferentiability

/-- The weight of a path whose vertices follow a formula is the sum over the formula. -/
theorem path_weight_eq_sum_of_vertex_formula (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (q : Path u d) (F : ℕ → Lattice) (hv : ∀ k : Fin (d.1 + d.2 + 1), q.vertex k = F k.val) :
    pathWeight ω q = ∑ i ∈ Finset.range (d.1 + d.2), ω (F i) := by
  unfold pathWeight
  rw [← Fin.sum_univ_eq_sum_range (fun i => ω (F i)) (d.1 + d.2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hv i.castSucc]
  rfl

/-- **The fine count (5.15), deterministic form.** Representative values of `ρ` in the bin. -/
theorem fine_staircase_representatives (a : ℝ) (I : ℤ) (l w : ℕ) (hw : 0 < w) (h : ℤ) :
    ∃ R : Finset ℝ, (R.card : ℝ) ≤ ((l : ℝ) + 1) * w + 1 ∧
      (∀ ρ ∈ R, (h : ℝ) * w ≤ ρ ∧ ρ < ((h : ℝ) + 1) * w) ∧
      ∀ ρ : ℝ, (h : ℝ) * w ≤ ρ → ρ < ((h : ℝ) + 1) * w →
        ∃ ρ' ∈ R, ∀ i : ℕ, i ≤ l →
          ⌊ρ + a * ((I + (i : ℤ) : ℤ) : ℝ)⌋ = ⌊ρ' + a * ((I + (i : ℤ) : ℤ) : ℝ)⌋ := by
  classical
  set x : ℕ → ℝ := fun i => (h : ℝ) * w + a * ((I + (i : ℤ) : ℤ) : ℝ) with hx
  set T : ℕ → Finset ℝ := fun i => (Finset.Ico ⌈x i⌉ ⌈x i + w⌉).image
    (fun n : ℤ => (n : ℝ) - a * ((I + (i : ℤ) : ℤ) : ℝ)) with hT
  set R : Finset ℝ := insert ((h : ℝ) * w) ((Finset.range (l + 1)).biUnion T) with hR
  have hmem : ∀ ρ : ℝ, ρ ∈ R ↔ ρ = (h : ℝ) * w ∨ ∃ i, i < l + 1 ∧ ∃ n : ℤ,
      ⌈x i⌉ ≤ n ∧ n < ⌈x i + w⌉ ∧ (n : ℝ) - a * ((I + (i : ℤ) : ℤ) : ℝ) = ρ := by
    intro ρ
    simp only [hR, hT, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro (h1 | ⟨i, hi, n, ⟨hn1, hn2⟩, hn3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨i, hi, n, hn1, hn2, hn3⟩
    · rintro (h1 | ⟨i, hi, n, hn1, hn2, hn3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨i, hi, n, ⟨hn1, hn2⟩, hn3⟩
  have hbin : ∀ ρ ∈ R, (h : ℝ) * w ≤ ρ ∧ ρ < ((h : ℝ) + 1) * w := by
    intro ρ hρ
    rcases (hmem ρ).1 hρ with rfl | ⟨i, hi, n, hn1, hn2, rfl⟩
    · have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
      constructor <;> nlinarith
    · have h1 : x i ≤ n := Int.ceil_le.1 hn1
      have h2 : (n : ℝ) < x i + w := Int.lt_ceil.1 hn2
      simp only [hx] at h1 h2
      constructor <;> nlinarith
  refine ⟨R, ?_, hbin, ?_⟩
  · have hN : ∀ i, (Finset.Ico ⌈x i⌉ ⌈x i + w⌉).card = w := by
      intro i
      rw [Int.card_Ico, Int.ceil_add_natCast]
      omega
    have h1 : R.card ≤ (l + 1) * w + 1 := by
      calc R.card ≤ ((Finset.range (l + 1)).biUnion T).card + 1 := Finset.card_insert_le _ _
        _ ≤ (∑ i ∈ Finset.range (l + 1), (T i).card) + 1 :=
            Nat.add_le_add_right Finset.card_biUnion_le 1
        _ ≤ (∑ i ∈ Finset.range (l + 1), w) + 1 := by
            refine Nat.add_le_add_right (Finset.sum_le_sum fun i _ => ?_) 1
            exact Finset.card_image_le.trans (hN i).le
        _ = (l + 1) * w + 1 := by simp
    exact_mod_cast h1
  · intro ρ hρ1 hρ2
    have hne : (R.filter (· ≤ ρ)).Nonempty :=
      ⟨(h : ℝ) * w, Finset.mem_filter.2 ⟨(hmem _).2 (Or.inl rfl), hρ1⟩⟩
    have hmx : (R.filter (· ≤ ρ)).max' hne ∈ R.filter (· ≤ ρ) := Finset.max'_mem _ _
    obtain ⟨hmR, hmle⟩ := Finset.mem_filter.1 hmx
    refine ⟨_, hmR, fun i hi => ?_⟩
    set ρ' := (R.filter (· ≤ ρ)).max' hne with hρ'
    by_contra hne2
    have hlt : ⌊ρ' + a * ((I + (i : ℤ) : ℤ) : ℝ)⌋ < ⌊ρ + a * ((I + (i : ℤ) : ℤ) : ℝ)⌋ :=
      lt_of_le_of_ne (Int.floor_mono (by linarith)) (fun e => hne2 e.symm)
    set n := ⌊ρ + a * ((I + (i : ℤ) : ℤ) : ℝ)⌋ with hn
    have hn1 : (n : ℝ) ≤ ρ + a * ((I + (i : ℤ) : ℤ) : ℝ) := Int.floor_le _
    have hn2 : ρ' + a * ((I + (i : ℤ) : ℤ) : ℝ) < n := by
      have h1 := Int.lt_floor_add_one (ρ' + a * ((I + (i : ℤ) : ℤ) : ℝ))
      have h2 : ((⌊ρ' + a * ((I + (i : ℤ) : ℤ) : ℝ)⌋ : ℤ) : ℝ) + 1 ≤ n := by exact_mod_cast hlt
      linarith
    have hρ'b := (hbin ρ' hmR).1
    have hmem' : (n : ℝ) - a * ((I + (i : ℤ) : ℤ) : ℝ) ∈ R := by
      refine (hmem _).2 (Or.inr ⟨i, by omega, n, ?_, ?_, rfl⟩)
      · exact Int.ceil_le.2 (by simp only [hx]; linarith)
      · exact Int.lt_ceil.2 (by simp only [hx]; nlinarith)
    have hle : (n : ℝ) - a * ((I + (i : ℤ) : ℤ) : ℝ) ≤ ρ' :=
      Finset.le_max' _ _ (Finset.mem_filter.2 ⟨hmem', by linarith⟩)
    linarith

/-- Lattice sites on level `L` whose transverse coordinate lies strictly between `p` and
`p + n`: at most `n` of them. -/
theorem level_points_open (a : ℝ) (L : ℤ) (p : ℝ) (n : ℕ) :
    ∃ S : Finset Lattice, S.card ≤ n ∧ ∀ z : Lattice, z ∈ S ↔
      z.1 + z.2 = L ∧ p < (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) ∧
        (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) < p + n := by
  classical
  refine ⟨(Finset.Ioo ⌊p + a * (L : ℝ)⌋ ⌈p + a * (L : ℝ) + n⌉).image
    (fun x : ℤ => (x, L - x)), ?_, fun z => ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Int.card_Ioo, Int.ceil_add_natCast]
    have := Int.ceil_le_floor_add_one (p + a * (L : ℝ))
    omega
  · simp only [Finset.mem_image, Finset.mem_Ioo]
    constructor
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      have h1' := Int.floor_lt.1 h1
      have h2' := Int.lt_ceil.1 h2
      refine ⟨by simp, ?_, ?_⟩ <;> push_cast <;> nlinarith
    · rintro ⟨hl, h1, h2⟩
      have hz2 : z.2 = L - z.1 := by omega
      have hz2R : (z.2 : ℝ) = (L : ℝ) - z.1 := by exact_mod_cast hz2
      refine ⟨z.1, ⟨Int.floor_lt.2 ?_, Int.lt_ceil.2 ?_⟩, ?_⟩
      · rw [hz2R] at h1; nlinarith
      · rw [hz2R] at h2; nlinarith
      · exact Prod.ext rfl hz2.symm

/-- Lattice sites on level `L` whose transverse coordinate lies in `[q, q + n]`: at most
`n + 1` of them. -/
theorem level_points_closed (a : ℝ) (L : ℤ) (q : ℝ) (n : ℕ) :
    ∃ S : Finset Lattice, S.card ≤ n + 1 ∧ ∀ z : Lattice, z ∈ S ↔
      z.1 + z.2 = L ∧ q ≤ (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) ∧
        (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) ≤ q + n := by
  classical
  refine ⟨(Finset.Icc ⌈q + a * (L : ℝ)⌉ ⌊q + a * (L : ℝ) + n⌋).image
    (fun x : ℤ => (x, L - x)), ?_, fun z => ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Int.card_Icc, Int.floor_add_natCast]
    have := Int.floor_le_ceil (q + a * (L : ℝ))
    omega
  · simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      have h1' := Int.ceil_le.1 h1
      have h2' := Int.le_floor.1 h2
      refine ⟨by simp, ?_, ?_⟩ <;> push_cast <;> nlinarith
    · rintro ⟨hl, h1, h2⟩
      have hz2 : z.2 = L - z.1 := by omega
      have hz2R : (z.2 : ℝ) = (L : ℝ) - z.1 := by exact_mod_cast hz2
      refine ⟨z.1, ⟨Int.ceil_le.2 ?_, Int.le_floor.2 ?_⟩, ?_⟩
      · rw [hz2R] at h1; nlinarith
      · rw [hz2R] at h2; nlinarith
      · exact Prod.ext rfl hz2.symm

/-- The natural displacement from `p` to `q`, correct whenever `p + d = q` with `d` natural. -/
private def disp (p q : Lattice) : ℕ × ℕ := ((q.1 - p.1).toNat, (q.2 - p.2).toNat)

private theorem disp_eq {p q : Lattice} {d : ℕ × ℕ} (h : p + ((d.1 : ℤ), (d.2 : ℤ)) = q) :
    disp p q = d := by
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp only [Prod.fst_add, Prod.snd_add] at e1 e2
  exact Prod.ext (by simp only [disp]; omega) (by simp only [disp]; omega)

/-- **The staircase count (5.25), deterministic form.** All pairs (start, displacement) of the two
attachment staircases at a coarse scale, over the bin, the `j²` blocks and every crossing
endpoint, lie in one set of at most `2 (w + 1) j² (16 w + 2)` pairs. -/
theorem coarse_attachment_family (a : ℝ) (I : ℤ) (l m j w : ℕ) (h : ℤ)
    (c : Fin (j ^ 2) → Lattice) :
    ∃ F : Finset (Lattice × (ℕ × ℕ)), F.card ≤ 2 * (w + 1) * j ^ 2 * (16 * w + 2) ∧
      ∀ (ρ : ℝ), (h : ℝ) * w ≤ ρ → ρ < ((h : ℝ) + 1) * w →
        ∀ (z₀ z₁ u u' : Lattice) (d₁ d₂ : ℕ × ℕ) (ν : Fin (j ^ 2)),
        (z₀.1 + z₀.2 = I ∧ ρ - 1 < (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ∧
          (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ≤ ρ) →
        (z₁.1 + z₁.2 = I + (l : ℤ) ∧ ρ - 1 < (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ∧
          (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ≤ ρ) →
        u.1 + u.2 = I + (m : ℤ) → u'.1 + u'.2 = I + (l : ℤ) - (m : ℤ) →
        |(1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) -
          ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * (w : ℝ) →
        |(1 - a) * (u'.1 : ℝ) - a * (u'.2 : ℝ) -
          ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * (w : ℝ) →
        z₀ + ((d₁.1 : ℤ), (d₁.2 : ℤ)) = u → u' + ((d₂.1 : ℤ), (d₂.2 : ℤ)) = z₁ →
        (z₀, d₁) ∈ F ∧ (u', d₂) ∈ F := by
  classical
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  obtain ⟨Z0, hZ0c, hZ0⟩ := level_points_open a I ((h : ℝ) * w - 1) (w + 1)
  obtain ⟨Z1, hZ1c, hZ1⟩ := level_points_open a (I + (l : ℤ)) ((h : ℝ) * w - 1) (w + 1)
  have hUc : ∀ (L : ℤ), ∃ U : Fin (j ^ 2) → Finset Lattice, (∀ ν, (U ν).card ≤ 16 * w + 1) ∧
      ∀ ν z, z ∈ U ν ↔ z.1 + z.2 = L ∧
        |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) -
          ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * (w : ℝ) := by
    intro L
    choose U hUc hU using fun ν : Fin (j ^ 2) =>
      level_points_closed a L ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ) - 8 * (w : ℝ)) (16 * w)
    refine ⟨U, hUc, fun ν z => ?_⟩
    rw [hU ν z, abs_le]
    push_cast
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
  obtain ⟨U, hUcard, hU⟩ := hUc (I + (m : ℤ))
  obtain ⟨U', hU'card, hU'⟩ := hUc (I + (l : ℤ) - (m : ℤ))
  set Ub : Finset Lattice := Finset.univ.biUnion U with hUb
  set Ub' : Finset Lattice := Finset.univ.biUnion U' with hUb'
  have hUbc : ∀ (V : Fin (j ^ 2) → Finset Lattice), (∀ ν, (V ν).card ≤ 16 * w + 1) →
      (Finset.univ.biUnion V).card ≤ j ^ 2 * (16 * w + 2) := by
    intro V hV
    calc (Finset.univ.biUnion V).card ≤ ∑ ν : Fin (j ^ 2), (V ν).card := Finset.card_biUnion_le
      _ ≤ ∑ _ν : Fin (j ^ 2), (16 * w + 2) :=
          Finset.sum_le_sum fun ν _ => by have := hV ν; omega
      _ = j ^ 2 * (16 * w + 2) := by simp
  refine ⟨(Z0 ×ˢ Ub).image (fun p => (p.1, disp p.1 p.2)) ∪
    (Ub' ×ˢ Z1).image (fun p => (p.1, disp p.1 p.2)), ?_, ?_⟩
  · refine (Finset.card_union_le _ _).trans ?_
    have h1 : (Z0 ×ˢ Ub).card ≤ (w + 1) * (j ^ 2 * (16 * w + 2)) := by
      rw [Finset.card_product]
      exact Nat.mul_le_mul (by omega) (hUbc U hUcard)
    have h2 : (Ub' ×ˢ Z1).card ≤ (j ^ 2 * (16 * w + 2)) * (w + 1) := by
      rw [Finset.card_product]
      exact Nat.mul_le_mul (hUbc U' hU'card) (by omega)
    have h3 := Finset.card_image_le (s := Z0 ×ˢ Ub) (f := fun p => (p.1, disp p.1 p.2))
    have h4 := Finset.card_image_le (s := Ub' ×ˢ Z1) (f := fun p => (p.1, disp p.1 p.2))
    calc _ ≤ (w + 1) * (j ^ 2 * (16 * w + 2)) + (j ^ 2 * (16 * w + 2)) * (w + 1) := by omega
      _ = 2 * (w + 1) * j ^ 2 * (16 * w + 2) := by ring
  · intro ρ hρ1 hρ2 z₀ z₁ u u' d₁ d₂ ν hz₀ hz₁ hu hu' hru hru' hd₁ hd₂
    obtain ⟨hz₀l, hz₀a, hz₀b⟩ := hz₀
    obtain ⟨hz₁l, hz₁a, hz₁b⟩ := hz₁
    have hz₀m : z₀ ∈ Z0 := (hZ0 z₀).2 ⟨hz₀l, by linarith, by push_cast; linarith⟩
    have hz₁m : z₁ ∈ Z1 := (hZ1 z₁).2 ⟨hz₁l, by linarith, by push_cast; linarith⟩
    have hum : u ∈ Ub := Finset.mem_biUnion.2 ⟨ν, Finset.mem_univ _, (hU ν u).2 ⟨hu, hru⟩⟩
    have hum' : u' ∈ Ub' := Finset.mem_biUnion.2 ⟨ν, Finset.mem_univ _, (hU' ν u').2 ⟨hu', hru'⟩⟩
    constructor
    · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨(z₀, u), Finset.mem_product.2 ⟨hz₀m, hum⟩, ?_⟩)
      simp only [disp_eq hd₁]
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨(u', z₁), Finset.mem_product.2 ⟨hum', hz₁m⟩, ?_⟩)
      simp only [disp_eq hd₂]

end LPPDifferentiability
