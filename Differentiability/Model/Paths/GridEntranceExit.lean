/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.WeightConcat
public import Differentiability.Analysis.GridScaleSums
public import Differentiability.Analysis.MixedRadixLevelDecomposition
import LPP_Foundations.Model.Paths.WeightZero
import Differentiability.Model.Paths.DefectAlgebra
import Differentiability.Analysis.GridScaleCounts
import Mathlib.Tactic

/-! # Entrance and exit paths of a vertex

This is the proof of Proposition 5.9 of the differentiability preprint. For one environment in which
every grid interval `[I, I + l_{j,k}]` at every scale `J ≤ j ≤ j_*` is joined at every `ρ` with
`|ρ| ≤ R s_k` by a path with both defects at most `C₁ j² w_{j,k} + 2 t_k` and transverse error at
most `C₁ j² w_{j,k}` (the conclusion of Lemma 5.7 (i)), a vertex `u` with `|ℓ(u)| ≤ A L_k` and
`|r(u)| ≤ R s_k` has an entrance path from level `I⁻(u)` to `u` and an exit path from `u` to level
`I⁺(u)` (5.39), each with both defects at most `ε s_k / 8 + ε s_k / 16` (5.41) and all vertices
within `2 C₁ s_k` of `r(u)`. The decomposition is the mixed-radix one of `grid_mixed_radix_lower`
and `grid_mixed_radix_upper`.
-/

public section

open scoped BigOperators

namespace LPPDifferentiability

/-- Every vertex of a concatenation is a vertex of one of the two pieces. -/
private theorem concat_vertex_cases' {u : Lattice} {d e : ℕ × ℕ} (p : Path u d)
    (q : Path (u + ((d.1 : ℤ), (d.2 : ℤ))) e) (k : Fin ((d + e).1 + (d + e).2 + 1)) :
    (∃ i, (p.concat q).vertex k = p.vertex i) ∨ ∃ i, (p.concat q).vertex k = q.vertex i := by
  have hk := k.isLt
  simp only [Prod.fst_add, Prod.snd_add] at hk
  by_cases h : k.val < d.1 + d.2
  · exact Or.inl ⟨⟨k.val, by omega⟩, by simp [Path.concat, Path.concatVertex, h]⟩
  · exact Or.inr ⟨⟨k.val - (d.1 + d.2), by omega⟩, by simp [Path.concat, Path.concatVertex, h]⟩

/-- **Concatenation with exact defect additivity.** Two paths meeting at `z'` join to one
path from `z` whose literal defects (for both slopes) are the sums of the two pieces' and
each of whose vertices is a vertex of one of the pieces. -/
theorem exists_concat_defect_eq (ω : Environment) (a G0 dl dr : ℝ) {z z' : Lattice}
    {D D' : ℕ × ℕ} (y : Path z D) (hD : z + ((D.1 : ℤ), (D.2 : ℤ)) = z') (y' : Path z' D') :
    ∃ (E : ℕ × ℕ) (x : Path z E),
      z + ((E.1 : ℤ), (E.2 : ℤ)) = z' + ((D'.1 : ℤ), (D'.2 : ℤ)) ∧
      G0 * ((E.1 : ℝ) + (E.2 : ℝ)) + dl * ((1 - a) * (E.1 : ℝ) - a * (E.2 : ℝ)) -
          pathWeight ω x =
        (G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
          pathWeight ω y) +
        (G0 * ((D'.1 : ℝ) + (D'.2 : ℝ)) + dl * ((1 - a) * (D'.1 : ℝ) - a * (D'.2 : ℝ)) -
          pathWeight ω y') ∧
      G0 * ((E.1 : ℝ) + (E.2 : ℝ)) + dr * ((1 - a) * (E.1 : ℝ) - a * (E.2 : ℝ)) -
          pathWeight ω x =
        (G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
          pathWeight ω y) +
        (G0 * ((D'.1 : ℝ) + (D'.2 : ℝ)) + dr * ((1 - a) * (D'.1 : ℝ) - a * (D'.2 : ℝ)) -
          pathWeight ω y') ∧
      ∀ i, (∃ j, x.vertex i = y.vertex j) ∨ ∃ j, x.vertex i = y'.vertex j := by
  subst hD
  refine ⟨D + D', y.concat y', ?_, Path.path_support_defect_concat a G0 dl ω y y',
    Path.path_support_defect_concat a G0 dr ω y y', concat_vertex_cases' y y'⟩
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add] <;> ring

/-- The lattice point `ẑ(I, ρ)` of `stairdef`. -/
private noncomputable def zh (a ρ : ℝ) (I : ℤ) : Lattice := (⌊ρ + a * (I : ℝ)⌋, I - ⌊ρ + a * (I : ℝ)⌋)

private theorem zh_spec (a ρ : ℝ) (I : ℤ) :
    (zh a ρ I).1 + (zh a ρ I).2 = I ∧
      ρ - 1 < (1 - a) * ((zh a ρ I).1 : ℝ) - a * ((zh a ρ I).2 : ℝ) ∧
      (1 - a) * ((zh a ρ I).1 : ℝ) - a * ((zh a ρ I).2 : ℝ) ≤ ρ := by
  have h1 := Int.floor_le (ρ + a * (I : ℝ))
  have h2 := Int.lt_floor_add_one (ρ + a * (I : ℝ))
  have e : (1 - a) * ((zh a ρ I).1 : ℝ) - a * ((zh a ρ I).2 : ℝ) =
      (⌊ρ + a * (I : ℝ)⌋ : ℝ) - a * I := by
    simp only [zh]
    push_cast
    ring
  refine ⟨by simp only [zh]; ring, ?_, ?_⟩ <;> rw [e] <;> linarith

private theorem zh_unique (a ρ : ℝ) (z : Lattice)
    (h1 : ρ - 1 < (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ))
    (h2 : (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) ≤ ρ) : zh a ρ (z.1 + z.2) = z := by
  have e : (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) = z.1 - a * ((z.1 + z.2 : ℤ) : ℝ) := by
    push_cast
    ring
  have hf : ⌊ρ + a * ((z.1 + z.2 : ℤ) : ℝ)⌋ = z.1 := by
    rw [Int.floor_eq_iff]
    constructor <;> linarith
  simp only [zh, hf]
  apply Prod.ext <;> simp

/-- A connection from `z` to `z'` of cost at most `c` whose vertices are within `B` of `ρ`. -/
private def Conn (ω : Environment) (a G0 dl dr ρ B c : ℝ) (z z' : Lattice) : Prop :=
  ∃ (D : ℕ × ℕ) (y : Path z D), z + ((D.1 : ℤ), (D.2 : ℤ)) = z' ∧
    G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
      pathWeight ω y ≤ c ∧
    G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
      pathWeight ω y ≤ c ∧
    ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) - ρ| ≤ B

private theorem conn_trans {ω : Environment} {a G0 dl dr ρ B c c' : ℝ} {z z' z'' : Lattice}
    (h : Conn ω a G0 dl dr ρ B c z z') (h' : Conn ω a G0 dl dr ρ B c' z' z'') :
    Conn ω a G0 dl dr ρ B (c + c') z z'' := by
  obtain ⟨D, y, hD, h1, h2, h3⟩ := h
  obtain ⟨D', y', hD', h1', h2', h3'⟩ := h'
  obtain ⟨E, x, hE, e1, e2, hv⟩ := exists_concat_defect_eq ω a G0 dl dr y hD y'
  refine ⟨E, x, hE.trans hD', by linarith, by linarith, fun i => ?_⟩
  rcases hv i with ⟨j, hj⟩ | ⟨j, hj⟩ <;> rw [hj]
  · exact h3 j
  · exact h3' j

private theorem conn_mono {ω : Environment} {a G0 dl dr ρ B c c' : ℝ} {z z' : Lattice}
    (h : Conn ω a G0 dl dr ρ B c z z') (hc : c ≤ c') : Conn ω a G0 dl dr ρ B c' z z' := by
  obtain ⟨D, y, hD, h1, h2, h3⟩ := h
  exact ⟨D, y, hD, h1.trans hc, h2.trans hc, h3⟩

private theorem conn_refl (ω : Environment) (a G0 dl dr ρ B : ℝ) (z : Lattice)
    (hz : |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - ρ| ≤ B) :
    Conn ω a G0 dl dr ρ B 0 z z := by
  let y : Path z (0, 0) := ⟨fun _ => z, rfl, by ext <;> simp, fun i => i.elim0⟩
  refine ⟨(0, 0), y, by ext <;> simp, ?_, ?_, fun _ => hz⟩ <;>
    simp [pathWeight_zero]

/-- The entrance chain: from `ẑ(q J)` up to `ẑ(q j)` through the grid intervals. -/
private theorem entrance_chain (ω : Environment) (a G0 dl dr ρ B Gb : ℝ) (J jstar : ℕ)
    (l n : ℕ → ℕ) (q : ℕ → ℤ) (cst : ℕ → ℝ)
    (hpiece : ∀ j, J ≤ j → j ≤ jstar → ∀ I : ℤ, (l j : ℤ) ∣ I → |(I : ℝ)| ≤ Gb →
      Conn ω a G0 dl dr ρ B (cst j) (zh a ρ I) (zh a ρ (I + l j)))
    (htile : ∀ j, J ≤ j → j ≤ jstar → q (j + 1) = q j + n j * l j)
    (hmem : ∀ j, J ≤ j → j ≤ jstar → ∀ t, t < n j →
      (l j : ℤ) ∣ q j + t * l j ∧ |((q j + t * l j : ℤ) : ℝ)| ≤ Gb)
    (hB : |(1 - a) * ((zh a ρ (q J)).1 : ℝ) - a * ((zh a ρ (q J)).2 : ℝ) - ρ| ≤ B) :
    ∀ j, J ≤ j → j ≤ jstar + 1 → Conn ω a G0 dl dr ρ B
      (∑ i ∈ Finset.Ico J j, (n i : ℝ) * cst i) (zh a ρ (q J)) (zh a ρ (q j)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro _
    simpa using conn_refl ω a G0 dl dr ρ B _ hB
  | succ j hj ih =>
    intro hj1
    have inner : ∀ t, t ≤ n j → Conn ω a G0 dl dr ρ B
        ((∑ i ∈ Finset.Ico J j, (n i : ℝ) * cst i) + t * cst j)
        (zh a ρ (q J)) (zh a ρ (q j + t * l j)) := by
      intro t
      induction t with
      | zero => intro _; simpa using ih (by omega)
      | succ t iht =>
        intro ht
        obtain ⟨hd, hb⟩ := hmem j hj (by omega) t (by omega)
        have hc := conn_trans (iht (by omega)) (hpiece j hj (by omega) _ hd hb)
        have e : q j + (t : ℤ) * l j + l j = q j + ((t + 1 : ℕ) : ℤ) * l j := by
          push_cast; ring
        rw [e] at hc
        refine conn_mono hc (le_of_eq ?_)
        push_cast; ring
    have h := inner (n j) le_rfl
    rw [← htile j hj (by omega)] at h
    rwa [Finset.sum_Ico_succ_top hj]

/-- The exit chain: from `ẑ(q j)` up to `ẑ(q J)`, with `q` decreasing. -/
private theorem exit_chain (ω : Environment) (a G0 dl dr ρ B Gb : ℝ) (J jstar : ℕ)
    (l n : ℕ → ℕ) (q : ℕ → ℤ) (cst : ℕ → ℝ)
    (hpiece : ∀ j, J ≤ j → j ≤ jstar → ∀ I : ℤ, (l j : ℤ) ∣ I → |(I : ℝ)| ≤ Gb →
      Conn ω a G0 dl dr ρ B (cst j) (zh a ρ I) (zh a ρ (I + l j)))
    (htile : ∀ j, J ≤ j → j ≤ jstar → q (j + 1) = q j - n j * l j)
    (hmem : ∀ j, J ≤ j → j ≤ jstar → ∀ t, t < n j →
      (l j : ℤ) ∣ q j - (t + 1) * l j ∧ |((q j - (t + 1) * l j : ℤ) : ℝ)| ≤ Gb)
    (hB : |(1 - a) * ((zh a ρ (q J)).1 : ℝ) - a * ((zh a ρ (q J)).2 : ℝ) - ρ| ≤ B) :
    ∀ j, J ≤ j → j ≤ jstar + 1 → Conn ω a G0 dl dr ρ B
      (∑ i ∈ Finset.Ico J j, (n i : ℝ) * cst i) (zh a ρ (q j)) (zh a ρ (q J)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro _
    simpa using conn_refl ω a G0 dl dr ρ B _ hB
  | succ j hj ih =>
    intro hj1
    have inner : ∀ t, t ≤ n j → Conn ω a G0 dl dr ρ B
        ((∑ i ∈ Finset.Ico J j, (n i : ℝ) * cst i) + t * cst j)
        (zh a ρ (q j - t * l j)) (zh a ρ (q J)) := by
      intro t
      induction t with
      | zero => intro _; simpa using ih (by omega)
      | succ t iht =>
        intro ht
        obtain ⟨hd, hb⟩ := hmem j hj (by omega) t (by omega)
        have hp := hpiece j hj (by omega) _ hd hb
        have e : q j - ((t : ℤ) + 1) * l j + l j = q j - t * l j := by ring
        rw [e] at hp
        have hc := conn_trans hp (iht (by omega))
        have e' : q j - ((t : ℤ) + 1) * l j = q j - ((t + 1 : ℕ) : ℤ) * l j := by
          push_cast; ring
        rw [e'] at hc
        refine conn_mono hc (le_of_eq ?_)
        push_cast; ring
    have h := inner (n j) le_rfl
    rw [← htile j hj (by omega)] at h
    rwa [Finset.sum_Ico_succ_top hj]

/-- The total cost of a chain is the bound (5.41) of the differentiability preprint. -/
theorem chain_cost_le (c1 ε : ℝ) (k J jstar : ℕ) (n : ℕ → ℕ) (hc1 : 0 ≤ c1)
    (hε : 0 < ε) (hJ1 : 1 ≤ J) (hjk : jstar ≤ k) (hk : 0 < k) (hn1 : n J = 1)
    (hn15 : ∀ j, J < j → j ≤ jstar → n j ≤ 15)
    (hJε : 16 * c1 * ∑' i : ℕ, ((i + J : ℕ) : ℝ) ^ 2 / 2 ^ (i + J) ≤ ε / 8) :
    ∑ i ∈ Finset.Ico J (jstar + 1), (n i : ℝ) *
        (c1 * (i : ℝ) ^ 2 * 2 ^ (k - i) + 2 * ((ε / 512) * 2 ^ k / k)) ≤
      ε * 2 ^ k / 8 + ε * 2 ^ k / 16 := by
  classical
  let n' : ℕ → ℕ := fun j => if J ≤ j ∧ j ≤ jstar then n j else 0
  have hn' : ∀ j, n' j ≤ 16 := by
    intro j
    simp only [n']
    split_ifs with h
    · rcases Nat.eq_or_lt_of_le h.1 with h' | h'
      · subst h'; omega
      · have := hn15 j h' h.2; omega
    · omega
  have hIco : Finset.Ico J (jstar + 1) = Finset.Icc J jstar := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  have h := grid_extcost_le n' hc1 hε hn' hJ1 hjk hk hJε
  rw [hIco]
  refine (Finset.sum_congr rfl fun j hj => ?_).trans_le h
  have hj' := Finset.mem_Icc.1 hj
  simp [n', hj']

/-- **Entrance and exit paths of a vertex `u`** (equations (5.39)-(5.41) of the differentiability
preprint), in one environment satisfying the conclusion of Lemma 5.7 (i) with constant `c1`,
`t_k = ε s_k / (512 k)`, scales `J ≤ j ≤ j_* = ⌈(M - 1)/4⌉`, meshes `2^(M - 4 j - 1)` and widths
`2^(k-j)`. -/
theorem grid_entrance_exit (ω : Environment) (a G0 dl dr c1 A R ε : ℝ) (M k J : ℕ)
    (hc1 : 1 ≤ c1) (hε : 0 < ε) (hJ1 : 1 ≤ J) (hJ : J ≤ ⌈((M : ℝ) - 1) / 4⌉₊)
    (hjk : ⌈((M : ℝ) - 1) / 4⌉₊ ≤ k) (hk : 0 < k)
    (hJε : 16 * c1 * ∑' i : ℕ, ((i + J : ℕ) : ℝ) ^ 2 / 2 ^ (i + J) ≤ ε / 8)
    (hconn : ∀ j : ℕ, J ≤ j → j ≤ ⌈((M : ℝ) - 1) / 4⌉₊ →
      ∀ I : ℤ, ((2 ^ (M - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ M →
      ∀ ρ : ℝ, |ρ| ≤ R * 2 ^ k → ∀ z₀ z₁ : Lattice,
      (z₀.1 + z₀.2 = I ∧ ρ - 1 < (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ∧
        (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ≤ ρ) →
      (z₁.1 + z₁.2 = I + ((2 ^ (M - 4 * j - 1) : ℕ) : ℤ) ∧
        ρ - 1 < (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ∧
        (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ≤ ρ) →
      ∃ (D : ℕ × ℕ) (y : Path z₀ D),
        z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
            pathWeight ω y ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε / 512 * 2 ^ k / (k : ℝ)) ∧
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
            pathWeight ω y ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε / 512 * 2 ^ k / (k : ℝ)) ∧
        ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) - ρ| ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)))
    (u : Lattice) (hul : |((u.1 + u.2 : ℤ) : ℝ)| ≤ A * 2 ^ M)
    (hur : |(1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)| ≤ R * 2 ^ k) :
    (∃ (z : Lattice) (D : ℕ × ℕ) (y : Path z D),
      z.1 + z.2 = (⌊((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (M - 4 * J - 1) : ℕ) : ℝ)⌋ - 1) *
        ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) ∧
      z + ((D.1 : ℤ), (D.2 : ℤ)) = u ∧
      G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
        pathWeight ω y ≤ ε * 2 ^ k / 8 + ε * 2 ^ k / 16 ∧
      G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
        pathWeight ω y ≤ ε * 2 ^ k / 8 + ε * 2 ^ k / 16 ∧
      ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) -
        ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤ 2 * c1 * 2 ^ k) ∧
    (∃ (D : ℕ × ℕ) (y : Path u D),
      u.1 + u.2 + D.1 + D.2 =
        (⌈((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (M - 4 * J - 1) : ℕ) : ℝ)⌉ + 1) *
          ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) ∧
      G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
        pathWeight ω y ≤ ε * 2 ^ k / 8 + ε * 2 ^ k / 16 ∧
      G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
        pathWeight ω y ≤ ε * 2 ^ k / 8 + ε * 2 ^ k / 16 ∧
      ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) -
        ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤ 2 * c1 * 2 ^ k) := by
  set ρ : ℝ := (1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) with hρ
  set jstar : ℕ := ⌈((M : ℝ) - 1) / 4⌉₊ with hjstar
  let l : ℕ → ℕ := fun j => 2 ^ (M - 4 * j - 1)
  let cst : ℕ → ℝ := fun j => c1 * (j : ℝ) ^ 2 * 2 ^ (k - j) + 2 * ((ε / 512) * 2 ^ k / k)
  set B : ℝ := 2 * c1 * 2 ^ k with hB
  have hB1 : 1 ≤ B := by
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    rw [hB]; nlinarith
  have hpiece : ∀ j, J ≤ j → j ≤ jstar → ∀ I : ℤ, (l j : ℤ) ∣ I →
      |(I : ℝ)| ≤ (A + 4) * 2 ^ M →
      Conn ω a G0 dl dr ρ B (cst j) (zh a ρ I) (zh a ρ (I + l j)) := by
    intro j hJj hj I hd hI
    obtain ⟨D, y, hD, h1, h2, h3⟩ := hconn j hJj hj I hd hI ρ hur (zh a ρ I) (zh a ρ (I + l j))
      (zh_spec a ρ I) (zh_spec a ρ (I + l j))
    have hc : c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε / 512 * 2 ^ k / (k : ℝ)) =
        cst j := by
      simp only [cst]; push_cast; ring
    have hw : (j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ) ≤ 2 * 2 ^ k := by
      have := grid_sq_mul_width_le (hj.trans hjk)
      exact_mod_cast this
    have hw' : c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) ≤ B := by
      have := mul_le_mul_of_nonneg_left hw (by linarith : (0 : ℝ) ≤ c1)
      rw [hB]; linarith
    exact ⟨D, y, hD, by linarith, by linarith, fun i => (h3 i).trans hw'⟩
  have hzB : ∀ I, |(1 - a) * ((zh a ρ I).1 : ℝ) - a * ((zh a ρ I).2 : ℝ) - ρ| ≤ B := by
    intro I
    obtain ⟨-, h1, h2⟩ := zh_spec a ρ I
    rw [abs_le]; constructor <;> linarith
  have hu : zh a ρ (u.1 + u.2) = u := zh_unique a ρ u (by linarith) le_rfl
  have hcost := fun (n : ℕ → ℕ) (hn1 : n J = 1) (hn15 : ∀ j, J < j → j ≤ jstar → n j ≤ 15) =>
    chain_cost_le c1 ε k J jstar n (by linarith) hε hJ1 hjk hk hn1 hn15 hJε
  constructor
  · obtain ⟨n, q, hqJ, hn1, hn15, htile, hend, hmem⟩ :=
      grid_mixed_radix_lower (A := A) hjstar l (fun _ => rfl) hJ hul
    have hc := entrance_chain ω a G0 dl dr ρ B ((A + 4) * 2 ^ M) J jstar l n q cst hpiece
      (fun j h1 h2 => (htile j h1 h2).1) (fun j h1 h2 t ht => ⟨(hmem j h1 h2 t ht).1,
        (hmem j h1 h2 t ht).2.1⟩) (hzB _) (jstar + 1) (by omega) le_rfl
    rw [hend, hu] at hc
    obtain ⟨D, y, hD, h1, h2, h3⟩ := conn_mono hc (hcost n hn1 hn15)
    refine ⟨zh a ρ (q J), D, y, ?_, hD, h1, h2, h3⟩
    rw [(zh_spec a ρ (q J)).1]
    exact hqJ
  · obtain ⟨n, q, hqJ, hn1, hn15, htile, hend, hmem⟩ :=
      grid_mixed_radix_upper (A := A) hjstar l (fun _ => rfl) hJ hul
    have hc := exit_chain ω a G0 dl dr ρ B ((A + 4) * 2 ^ M) J jstar l n q cst hpiece
      (fun j h1 h2 => (htile j h1 h2).1) (fun j h1 h2 t ht => ⟨(hmem j h1 h2 t ht).1,
        (hmem j h1 h2 t ht).2.1⟩) (hzB _) (jstar + 1) (by omega) le_rfl
    rw [hend, hu] at hc
    obtain ⟨D, y, hD, h1, h2, h3⟩ := conn_mono hc (hcost n hn1 hn15)
    refine ⟨D, y, ?_, h1, h2, h3⟩
    have hl := (zh_spec a ρ (q J)).1
    have e1 := congrArg Prod.fst hD
    have e2 := congrArg Prod.snd hD
    simp only [Prod.fst_add, Prod.snd_add] at e1 e2
    have hX : q J = (⌈((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (M - 4 * J - 1) : ℕ) : ℝ)⌉ + 1) *
        ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) := hqJ
    linarith

end LPPDifferentiability
