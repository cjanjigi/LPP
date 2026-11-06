/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.GridEntranceExit
public import LPP_Foundations.Model.Paths.WeightConcat
public import Differentiability.Analysis.GridScaleSums
public import Differentiability.Analysis.MixedRadixLevelDecomposition
import LPP_Foundations.Model.Paths.WeightZero
import Differentiability.Analysis.GridScaleCounts
import Mathlib.Tactic

/-! # Entrance and exit chains for a general point function

This is the endpoint argument of Proposition 5.9 of the differentiability preprint, with item (C8)
of Appendix B, for a general point function. The entrance and exit paths of a vertex `u` are built
along the points `ẑ(I, r(u))`, using them only through two facts: consecutive points are joined by
the per-interval paths, and the last point is `u`. Here the points are an arbitrary function
`P : ℤ → Lattice` of the grid levels (in the general case, the vertices of the greedy staircase
through `u`). The per-interval connections are hypotheses. Each theorem has the conclusion of
`grid_entrance_exit` for one side: cost at most `ε s_k / 8 + ε s_k / 16` (5.41 of the
differentiability preprint) and all vertices within `2 c₁ s_k` of `r(u)`.
-/

public section

open scoped BigOperators

namespace LPPDifferentiability

/-- A connection from `z` to `z'` of cost at most `c` whose vertices are within `B` of `ρ`. -/
private def PConn (ω : Environment) (a G0 dl dr ρ B c : ℝ) (z z' : Lattice) : Prop :=
  ∃ (D : ℕ × ℕ) (y : Path z D), z + ((D.1 : ℤ), (D.2 : ℤ)) = z' ∧
    G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
      pathWeight ω y ≤ c ∧
    G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
      pathWeight ω y ≤ c ∧
    ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) - ρ| ≤ B

private theorem pconn_trans {ω : Environment} {a G0 dl dr ρ B c c' : ℝ} {z z' z'' : Lattice}
    (h : PConn ω a G0 dl dr ρ B c z z') (h' : PConn ω a G0 dl dr ρ B c' z' z'') :
    PConn ω a G0 dl dr ρ B (c + c') z z'' := by
  obtain ⟨D, y, hD, h1, h2, h3⟩ := h
  obtain ⟨D', y', hD', h1', h2', h3'⟩ := h'
  obtain ⟨E, x, hE, e1, e2, hv⟩ := exists_concat_defect_eq ω a G0 dl dr y hD y'
  refine ⟨E, x, hE.trans hD', by linarith, by linarith, fun i => ?_⟩
  rcases hv i with ⟨j, hj⟩ | ⟨j, hj⟩ <;> rw [hj]
  · exact h3 j
  · exact h3' j

private theorem pconn_mono {ω : Environment} {a G0 dl dr ρ B c c' : ℝ} {z z' : Lattice}
    (h : PConn ω a G0 dl dr ρ B c z z') (hc : c ≤ c') : PConn ω a G0 dl dr ρ B c' z z' := by
  obtain ⟨D, y, hD, h1, h2, h3⟩ := h
  exact ⟨D, y, hD, h1.trans hc, h2.trans hc, h3⟩

private theorem pconn_refl (ω : Environment) (a G0 dl dr ρ B : ℝ) (z : Lattice)
    (hz : |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - ρ| ≤ B) :
    PConn ω a G0 dl dr ρ B 0 z z := by
  let y : Path z (0, 0) := ⟨fun _ => z, rfl, by ext <;> simp, fun i => i.elim0⟩
  refine ⟨(0, 0), y, by ext <;> simp, ?_, ?_, fun _ => hz⟩ <;>
    simp [pathWeight_zero]

/-- The start vertex of a connection is within the location bound. -/
private theorem pconn_start_le {ω : Environment} {a G0 dl dr ρ B c : ℝ} {z z' : Lattice}
    (h : PConn ω a G0 dl dr ρ B c z z') :
    |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - ρ| ≤ B := by
  obtain ⟨D, y, -, -, -, h3⟩ := h
  have := h3 0
  rwa [y.start] at this

/-- The end vertex of a connection is within the location bound. -/
private theorem pconn_end_le {ω : Environment} {a G0 dl dr ρ B c : ℝ} {z z' : Lattice}
    (h : PConn ω a G0 dl dr ρ B c z z') :
    |(1 - a) * (z'.1 : ℝ) - a * (z'.2 : ℝ) - ρ| ≤ B := by
  obtain ⟨D, y, hD, -, -, h3⟩ := h
  have := h3 (Fin.last _)
  rwa [y.finish, hD] at this

/-- The entrance chain: from `P (q J)` to `P (q j)` through the grid intervals. -/
private theorem entrance_chain_pts (ω : Environment) (a G0 dl dr ρ B Gb : ℝ) (J jstar : ℕ)
    (l n : ℕ → ℕ) (q : ℕ → ℤ) (cst : ℕ → ℝ) (P : ℤ → Lattice) (lo hi : ℤ)
    (hpiece : ∀ j, J ≤ j → j ≤ jstar → ∀ I : ℤ, (l j : ℤ) ∣ I → |(I : ℝ)| ≤ Gb →
      lo ≤ I → I + l j ≤ hi → PConn ω a G0 dl dr ρ B (cst j) (P I) (P (I + l j)))
    (htile : ∀ j, J ≤ j → j ≤ jstar → q (j + 1) = q j + n j * l j)
    (hmem : ∀ j, J ≤ j → j ≤ jstar → ∀ t, t < n j →
      (l j : ℤ) ∣ q j + t * l j ∧ |((q j + t * l j : ℤ) : ℝ)| ≤ Gb ∧ lo ≤ q j + t * l j ∧
        q j + (t + 1) * l j ≤ hi)
    (hB : |(1 - a) * ((P (q J)).1 : ℝ) - a * ((P (q J)).2 : ℝ) - ρ| ≤ B) :
    ∀ j, J ≤ j → j ≤ jstar + 1 → PConn ω a G0 dl dr ρ B
      (∑ i ∈ Finset.Ico J j, (n i : ℝ) * cst i) (P (q J)) (P (q j)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro _
    simpa using pconn_refl ω a G0 dl dr ρ B _ hB
  | succ j hj ih =>
    intro hj1
    have inner : ∀ t, t ≤ n j → PConn ω a G0 dl dr ρ B
        ((∑ i ∈ Finset.Ico J j, (n i : ℝ) * cst i) + t * cst j)
        (P (q J)) (P (q j + t * l j)) := by
      intro t
      induction t with
      | zero => intro _; simpa using ih (by omega)
      | succ t iht =>
        intro ht
        obtain ⟨hd, hb, hlo, hhi⟩ := hmem j hj (by omega) t (by omega)
        have e : q j + (t : ℤ) * l j + l j = q j + ((t + 1 : ℕ) : ℤ) * l j := by
          push_cast; ring
        have hc := pconn_trans (iht (by omega))
          (hpiece j hj (by omega) _ hd hb hlo (by rw [e]; push_cast at hhi ⊢; linarith))
        rw [e] at hc
        refine pconn_mono hc (le_of_eq ?_)
        push_cast; ring
    have h := inner (n j) le_rfl
    rw [← htile j hj (by omega)] at h
    rwa [Finset.sum_Ico_succ_top hj]

/-- The exit chain: from `P (q j)` to `P (q J)`, with `q` decreasing. -/
private theorem exit_chain_pts (ω : Environment) (a G0 dl dr ρ B Gb : ℝ) (J jstar : ℕ)
    (l n : ℕ → ℕ) (q : ℕ → ℤ) (cst : ℕ → ℝ) (P : ℤ → Lattice) (lo hi : ℤ)
    (hpiece : ∀ j, J ≤ j → j ≤ jstar → ∀ I : ℤ, (l j : ℤ) ∣ I → |(I : ℝ)| ≤ Gb →
      lo ≤ I → I + l j ≤ hi → PConn ω a G0 dl dr ρ B (cst j) (P I) (P (I + l j)))
    (htile : ∀ j, J ≤ j → j ≤ jstar → q (j + 1) = q j - n j * l j)
    (hmem : ∀ j, J ≤ j → j ≤ jstar → ∀ t, t < n j →
      (l j : ℤ) ∣ q j - (t + 1) * l j ∧ |((q j - (t + 1) * l j : ℤ) : ℝ)| ≤ Gb ∧
        lo ≤ q j - (t + 1) * l j ∧ q j - t * l j ≤ hi)
    (hB : |(1 - a) * ((P (q J)).1 : ℝ) - a * ((P (q J)).2 : ℝ) - ρ| ≤ B) :
    ∀ j, J ≤ j → j ≤ jstar + 1 → PConn ω a G0 dl dr ρ B
      (∑ i ∈ Finset.Ico J j, (n i : ℝ) * cst i) (P (q j)) (P (q J)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro _
    simpa using pconn_refl ω a G0 dl dr ρ B _ hB
  | succ j hj ih =>
    intro hj1
    have inner : ∀ t, t ≤ n j → PConn ω a G0 dl dr ρ B
        ((∑ i ∈ Finset.Ico J j, (n i : ℝ) * cst i) + t * cst j)
        (P (q j - t * l j)) (P (q J)) := by
      intro t
      induction t with
      | zero => intro _; simpa using ih (by omega)
      | succ t iht =>
        intro ht
        obtain ⟨hd, hb, hlo, hhi⟩ := hmem j hj (by omega) t (by omega)
        have e : q j - ((t : ℤ) + 1) * l j + l j = q j - t * l j := by ring
        have hp := hpiece j hj (by omega) _ hd hb hlo (by rw [e]; exact hhi)
        rw [e] at hp
        have hc := pconn_trans hp (iht (by omega))
        have e' : q j - ((t : ℤ) + 1) * l j = q j - ((t + 1 : ℕ) : ℤ) * l j := by
          push_cast; ring
        rw [e'] at hc
        refine pconn_mono hc (le_of_eq ?_)
        push_cast; ring
    have h := inner (n j) le_rfl
    rw [← htile j hj (by omega)] at h
    rwa [Finset.sum_Ico_succ_top hj]

/-- The breakpoints of an entrance decomposition are nondecreasing. -/
private theorem q_mono_up (J jstar : ℕ) (l n : ℕ → ℕ) (q : ℕ → ℤ)
    (htile : ∀ j, J ≤ j → j ≤ jstar → q (j + 1) = q j + n j * l j) :
    ∀ j, J ≤ j → j ≤ jstar + 1 → q J ≤ q j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hj ih =>
    intro hj1
    have h1 := ih (by omega)
    have h2 := htile j hj (by omega)
    have h3 : (0 : ℤ) ≤ (n j : ℤ) * (l j : ℤ) := by positivity
    linarith

/-- The breakpoints of an exit decomposition are nonincreasing. -/
private theorem q_mono_down (J jstar : ℕ) (l n : ℕ → ℕ) (q : ℕ → ℤ)
    (htile : ∀ j, J ≤ j → j ≤ jstar → q (j + 1) = q j - n j * l j) :
    ∀ j, J ≤ j → j ≤ jstar + 1 → q j ≤ q J := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hj ih =>
    intro hj1
    have h1 := ih (by omega)
    have h2 := htile j hj (by omega)
    have h3 : (0 : ℤ) ≤ (n j : ℤ) * (l j : ℤ) := by positivity
    linarith

/-- **Entrance chain for a point function** (equations (5.39)-(5.41) and item (C8) of
Appendix B of the differentiability preprint).
If the points `P I` on the grid levels from `I⁻(u)` to `ℓ(u)` are joined interval by interval
(`hconn`, the conclusion of Lemma 5.7 (i) along `P`), `P` has `u` as its point on level `ℓ(u)`
(`hPu`) and `P I` lies on level `I` (`hlev`), then `u` has an entrance path from `P I⁻` with both
defects at most `ε s_k / 8 + ε s_k / 16` (5.41) and all vertices within `2 c₁ s_k` of `r(u)`.
-/
theorem grid_entrance_chain_of_points (ω : Environment) (a G0 dl dr c1 A ε : ℝ) (M k J : ℕ)
    (P : ℤ → Lattice) (u : Lattice)
    (hc1 : 0 ≤ c1) (hε : 0 < ε) (hJ1 : 1 ≤ J) (hJ : J ≤ ⌈((M : ℝ) - 1) / 4⌉₊)
    (hjk : ⌈((M : ℝ) - 1) / 4⌉₊ ≤ k) (hk : 0 < k)
    (hJε : 16 * c1 * ∑' i : ℕ, ((i + J : ℕ) : ℝ) ^ 2 / 2 ^ (i + J) ≤ ε / 8)
    (hul : |((u.1 + u.2 : ℤ) : ℝ)| ≤ A * 2 ^ M)
    (hPu : P (u.1 + u.2) = u)
    (hlev : ∀ I : ℤ, I ≤ u.1 + u.2 → (P I).1 + (P I).2 = I)
    (hconn : ∀ j : ℕ, J ≤ j → j ≤ ⌈((M : ℝ) - 1) / 4⌉₊ →
      ∀ I : ℤ, ((2 ^ (M - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ M →
      (⌊((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (M - 4 * J - 1) : ℕ) : ℝ)⌋ - 1) *
        ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) ≤ I →
      I + ((2 ^ (M - 4 * j - 1) : ℕ) : ℤ) ≤ u.1 + u.2 →
      ∀ z₀ z₁ : Lattice, z₀ = P I → z₁ = P (I + ((2 ^ (M - 4 * j - 1) : ℕ) : ℤ)) →
      ∃ (D : ℕ × ℕ) (y : Path z₀ D),
        z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
            pathWeight ω y ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε / 512 * 2 ^ k / (k : ℝ)) ∧
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
            pathWeight ω y ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε / 512 * 2 ^ k / (k : ℝ)) ∧
        ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) -
            ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ))) :
    ∃ (z : Lattice) (D : ℕ × ℕ) (y : Path z D),
      z = P ((⌊((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (M - 4 * J - 1) : ℕ) : ℝ)⌋ - 1) *
        ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ)) ∧
      z.1 + z.2 = (⌊((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (M - 4 * J - 1) : ℕ) : ℝ)⌋ - 1) *
        ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) ∧
      z + ((D.1 : ℤ), (D.2 : ℤ)) = u ∧
      G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
        pathWeight ω y ≤ ε * 2 ^ k / 8 + ε * 2 ^ k / 16 ∧
      G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
        pathWeight ω y ≤ ε * 2 ^ k / 8 + ε * 2 ^ k / 16 ∧
      ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) -
        ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤ 2 * c1 * 2 ^ k := by
  set ρ : ℝ := (1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) with hρ
  set jstar : ℕ := ⌈((M : ℝ) - 1) / 4⌉₊ with hjstar
  let l : ℕ → ℕ := fun j => 2 ^ (M - 4 * j - 1)
  let cst : ℕ → ℝ := fun j => c1 * (j : ℝ) ^ 2 * 2 ^ (k - j) + 2 * ((ε / 512) * 2 ^ k / k)
  set B : ℝ := 2 * c1 * 2 ^ k with hB
  obtain ⟨n, q, hqJ, hn1, hn15, htile, hend, hmem⟩ :=
    grid_mixed_radix_lower (A := A) hjstar l (fun _ => rfl) hJ hul
  have hmono := q_mono_up J jstar l n q (fun j h1 h2 => (htile j h1 h2).1)
  have hqend : q J ≤ u.1 + u.2 := by
    have := hmono (jstar + 1) (by omega) le_rfl
    rwa [hend] at this
  have hpiece : ∀ j, J ≤ j → j ≤ jstar → ∀ I : ℤ, (l j : ℤ) ∣ I →
      |(I : ℝ)| ≤ (A + 4) * 2 ^ M → q J ≤ I → I + l j ≤ u.1 + u.2 →
      PConn ω a G0 dl dr ρ B (cst j) (P I) (P (I + l j)) := by
    intro j hJj hj I hd hI hlo hhi
    obtain ⟨D, y, hD, h1, h2, h3⟩ := hconn j hJj hj I hd hI (hqJ ▸ hlo) hhi (P I)
      (P (I + l j)) rfl rfl
    have hc : c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε / 512 * 2 ^ k / (k : ℝ)) =
        cst j := by
      simp only [cst]; push_cast; ring
    have hw : (j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ) ≤ 2 * 2 ^ k := by
      have := grid_sq_mul_width_le (hj.trans hjk)
      exact_mod_cast this
    have hw' : c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) ≤ B := by
      have := mul_le_mul_of_nonneg_left hw hc1
      rw [hB]; linarith
    exact ⟨D, y, hD, by linarith, by linarith, fun i => (h3 i).trans hw'⟩
  have hmem' : ∀ j, J ≤ j → j ≤ jstar → ∀ t, t < n j →
      (l j : ℤ) ∣ q j + t * l j ∧ |((q j + t * l j : ℤ) : ℝ)| ≤ (A + 4) * 2 ^ M ∧
        q J ≤ q j + t * l j ∧ q j + (t + 1) * l j ≤ u.1 + u.2 := by
    intro j hj1 hj2 t ht
    obtain ⟨h1, h2, h3⟩ := hmem j hj1 hj2 t ht
    have h4 := hmono j hj1 (by omega)
    have h5 : (0 : ℤ) ≤ (t : ℤ) * (l j : ℤ) := by positivity
    exact ⟨h1, h2, by linarith, h3⟩
  have hfirst : PConn ω a G0 dl dr ρ B (cst J) (P (q J)) (P (q J + l J)) := by
    obtain ⟨h1, h2, h3, h4⟩ := hmem' J le_rfl hJ 0 (by omega)
    simp only [Nat.cast_zero, zero_mul, add_zero, zero_add, one_mul] at h1 h2 h3 h4
    exact hpiece J le_rfl hJ (q J) h1 h2 le_rfl h4
  have hc := entrance_chain_pts ω a G0 dl dr ρ B ((A + 4) * 2 ^ M) J jstar l n q cst P (q J)
    (u.1 + u.2) hpiece (fun j h1 h2 => (htile j h1 h2).1) hmem' (pconn_start_le hfirst)
    (jstar + 1) (by omega) le_rfl
  have hcost : ∑ i ∈ Finset.Ico J (jstar + 1), (n i : ℝ) * cst i ≤
      ε * 2 ^ k / 8 + ε * 2 ^ k / 16 :=
    chain_cost_le c1 ε k J jstar n hc1 hε hJ1 hjk hk hn1 hn15 hJε
  rw [hend, hPu] at hc
  obtain ⟨D, y, hD, h1, h2, h3⟩ := pconn_mono hc hcost
  exact ⟨P (q J), D, y, by rw [hqJ], by rw [hlev _ hqend] ; exact hqJ, hD, h1, h2, h3⟩

/-- **Exit chain for a point function** (equations (5.39)-(5.41) and item (C8) of Appendix B),
the mirror image of `grid_entrance_chain_of_points`: the points `P I` on the grid levels from `ℓ(u)`
to `I⁺(u)` are joined interval by interval, and `u` has an exit path to `P I⁺`. -/
theorem grid_exit_chain_of_points (ω : Environment) (a G0 dl dr c1 A ε : ℝ) (M k J : ℕ)
    (P : ℤ → Lattice) (u : Lattice)
    (hc1 : 0 ≤ c1) (hε : 0 < ε) (hJ1 : 1 ≤ J) (hJ : J ≤ ⌈((M : ℝ) - 1) / 4⌉₊)
    (hjk : ⌈((M : ℝ) - 1) / 4⌉₊ ≤ k) (hk : 0 < k)
    (hJε : 16 * c1 * ∑' i : ℕ, ((i + J : ℕ) : ℝ) ^ 2 / 2 ^ (i + J) ≤ ε / 8)
    (hul : |((u.1 + u.2 : ℤ) : ℝ)| ≤ A * 2 ^ M)
    (hPu : P (u.1 + u.2) = u)
    (hlev : ∀ I : ℤ, u.1 + u.2 ≤ I → (P I).1 + (P I).2 = I)
    (hconn : ∀ j : ℕ, J ≤ j → j ≤ ⌈((M : ℝ) - 1) / 4⌉₊ →
      ∀ I : ℤ, ((2 ^ (M - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ M →
      u.1 + u.2 ≤ I →
      I + ((2 ^ (M - 4 * j - 1) : ℕ) : ℤ) ≤
        (⌈((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (M - 4 * J - 1) : ℕ) : ℝ)⌉ + 1) *
          ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) →
      ∀ z₀ z₁ : Lattice, z₀ = P I → z₁ = P (I + ((2 ^ (M - 4 * j - 1) : ℕ) : ℤ)) →
      ∃ (D : ℕ × ℕ) (y : Path z₀ D),
        z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
            pathWeight ω y ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε / 512 * 2 ^ k / (k : ℝ)) ∧
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
            pathWeight ω y ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε / 512 * 2 ^ k / (k : ℝ)) ∧
        ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) -
            ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ))) :
    ∃ (z : Lattice) (D : ℕ × ℕ) (y : Path u D),
      z = P ((⌈((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (M - 4 * J - 1) : ℕ) : ℝ)⌉ + 1) *
        ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ)) ∧
      z.1 + z.2 = (⌈((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (M - 4 * J - 1) : ℕ) : ℝ)⌉ + 1) *
        ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) ∧
      u + ((D.1 : ℤ), (D.2 : ℤ)) = z ∧
      G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
        pathWeight ω y ≤ ε * 2 ^ k / 8 + ε * 2 ^ k / 16 ∧
      G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
        pathWeight ω y ≤ ε * 2 ^ k / 8 + ε * 2 ^ k / 16 ∧
      ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) -
        ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤ 2 * c1 * 2 ^ k := by
  set ρ : ℝ := (1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) with hρ
  set jstar : ℕ := ⌈((M : ℝ) - 1) / 4⌉₊ with hjstar
  let l : ℕ → ℕ := fun j => 2 ^ (M - 4 * j - 1)
  let cst : ℕ → ℝ := fun j => c1 * (j : ℝ) ^ 2 * 2 ^ (k - j) + 2 * ((ε / 512) * 2 ^ k / k)
  set B : ℝ := 2 * c1 * 2 ^ k with hB
  obtain ⟨n, q, hqJ, hn1, hn15, htile, hend, hmem⟩ :=
    grid_mixed_radix_upper (A := A) hjstar l (fun _ => rfl) hJ hul
  have hmono := q_mono_down J jstar l n q (fun j h1 h2 => (htile j h1 h2).1)
  have hqend : u.1 + u.2 ≤ q J := by
    have := hmono (jstar + 1) (by omega) le_rfl
    rwa [hend] at this
  have hpiece : ∀ j, J ≤ j → j ≤ jstar → ∀ I : ℤ, (l j : ℤ) ∣ I →
      |(I : ℝ)| ≤ (A + 4) * 2 ^ M → u.1 + u.2 ≤ I → I + l j ≤ q J →
      PConn ω a G0 dl dr ρ B (cst j) (P I) (P (I + l j)) := by
    intro j hJj hj I hd hI hlo hhi
    obtain ⟨D, y, hD, h1, h2, h3⟩ := hconn j hJj hj I hd hI hlo (hhi.trans_eq hqJ) (P I)
      (P (I + l j)) rfl rfl
    have hc : c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε / 512 * 2 ^ k / (k : ℝ)) =
        cst j := by
      simp only [cst]; push_cast; ring
    have hw : (j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ) ≤ 2 * 2 ^ k := by
      have := grid_sq_mul_width_le (hj.trans hjk)
      exact_mod_cast this
    have hw' : c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) ≤ B := by
      have := mul_le_mul_of_nonneg_left hw hc1
      rw [hB]; linarith
    exact ⟨D, y, hD, by linarith, by linarith, fun i => (h3 i).trans hw'⟩
  have hmem' : ∀ j, J ≤ j → j ≤ jstar → ∀ t, t < n j →
      (l j : ℤ) ∣ q j - (t + 1) * l j ∧ |((q j - (t + 1) * l j : ℤ) : ℝ)| ≤ (A + 4) * 2 ^ M ∧
        u.1 + u.2 ≤ q j - (t + 1) * l j ∧ q j - t * l j ≤ q J := by
    intro j hj1 hj2 t ht
    obtain ⟨h1, h2, h3⟩ := hmem j hj1 hj2 t ht
    have h4 := hmono j hj1 (by omega)
    have h5 : (0 : ℤ) ≤ (t : ℤ) * (l j : ℤ) := by positivity
    exact ⟨h1, h2, h3, by linarith⟩
  have hfirst : PConn ω a G0 dl dr ρ B (cst J) (P (q J - l J)) (P (q J - l J + l J)) := by
    obtain ⟨h1, h2, h3, h4⟩ := hmem' J le_rfl hJ 0 (by omega)
    simp only [Nat.cast_zero, zero_mul, sub_zero, zero_add, one_mul] at h1 h2 h3 h4
    exact hpiece J le_rfl hJ (q J - l J) h1 h2 h3 (by linarith)
  have hB0 := pconn_end_le hfirst
  rw [sub_add_cancel] at hB0
  have hc := exit_chain_pts ω a G0 dl dr ρ B ((A + 4) * 2 ^ M) J jstar l n q cst P
    (u.1 + u.2) (q J) hpiece (fun j h1 h2 => (htile j h1 h2).1) hmem' hB0
    (jstar + 1) (by omega) le_rfl
  have hcost : ∑ i ∈ Finset.Ico J (jstar + 1), (n i : ℝ) * cst i ≤
      ε * 2 ^ k / 8 + ε * 2 ^ k / 16 :=
    chain_cost_le c1 ε k J jstar n hc1 hε hJ1 hjk hk hn1 hn15 hJε
  rw [hend, hPu] at hc
  obtain ⟨D, y, hD, h1, h2, h3⟩ := pconn_mono hc hcost
  exact ⟨P (q J), D, y, by rw [hqJ], by rw [hlev _ hqend]; exact hqJ, hD, h1, h2, h3⟩

end LPPDifferentiability
