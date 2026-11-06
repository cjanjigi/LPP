/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.OrientedPercolation
public import Differentiability.Model.OrientedPercolationLaws
public import Differentiability.Model.PercolationTriangles
public import LPP_Foundations.Model.LastPassage.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Passage times in the augmented process

This is the block form of the lemma behind the augmentation step. Every site occupied by
the augmented process at block `j` lies on level `j T`. It is reached from the start set by
a path whose passage time (start excluded, end included) is at least `j T + K (c₀ - 1)`,
where `K` is the number of augmentations made so far.

The proof is an induction on `j`. A step along an open path adds `T`, because every site
after the start has weight `1`. A triangle step adds `T + c₀ - 1`, by the triangle geometry
of the percolation triangles module. A step along an open path in which the counter also
went up is weaker than the claim, because `c₀ ≤ 1`.
-/

@[expose] public section

namespace LPPDifferentiability

/-! ## Gluing passage times -/

/-- Passage times, with the start excluded and the end included, add up at an
intermediate site, up to an inequality. -/
private theorem passage_add (ω : Environment) (u : Lattice) (d e : ℕ × ℕ) :
    (lastPassage ω u d - ω u + ω (u + ((d.1 : ℤ), (d.2 : ℤ)))) +
      (lastPassage ω (u + ((d.1 : ℤ), (d.2 : ℤ))) e - ω (u + ((d.1 : ℤ), (d.2 : ℤ))) +
        ω (u + ((d.1 : ℤ), (d.2 : ℤ)) + ((e.1 : ℤ), (e.2 : ℤ)))) ≤
      lastPassage ω u (d + e) - ω u +
        ω (u + ((d.1 : ℤ), (d.2 : ℤ)) + ((e.1 : ℤ), (e.2 : ℤ))) := by
  have h := lastPassage_superadditive ω u d e
  linarith

/-- If `r` is reached from `u` with passage time at least `b`, and `v` is reached from
`r` with passage time at least `c`, then `v` is reached from `u` with passage time at
least `b + c`. -/
private theorem extend_passage (ω : Environment) {u r v : Lattice} {d e : ℕ × ℕ} {b c : ℝ}
    (hd : u + ((d.1 : ℤ), (d.2 : ℤ)) = r) (he : r + ((e.1 : ℤ), (e.2 : ℤ)) = v)
    (hb : b ≤ lastPassage ω u d - ω u + ω r)
    (hc : c ≤ lastPassage ω r e - ω r + ω v) :
    ∃ d' : ℕ × ℕ, u + ((d'.1 : ℤ), (d'.2 : ℤ)) = v ∧
      b + c ≤ lastPassage ω u d' - ω u + ω v := by
  subst hd
  subst he
  refine ⟨d + e, ?_, ?_⟩
  · ext <;> simp [add_assoc]
  · have h := passage_add ω u d e
    linarith

/-- An open path of `T` steps collects `T` from the weights after its start. -/
private theorem open_passage (ω : Environment) (T : ℕ) (X : Set Lattice) (v : Lattice)
    (hv : v ∈ openReachSet (topSites ω) X T) :
    ∃ r ∈ X, ∃ e : ℕ × ℕ, r + ((e.1 : ℤ), (e.2 : ℤ)) = v ∧
      (T : ℝ) ≤ lastPassage ω r e - ω r + ω v := by
  obtain ⟨r, hr, ⟨d, hd, p, hp⟩, hl⟩ := hv
  have h1 := congrArg Prod.fst hd
  have h2 := congrArg Prod.snd hd
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  have hTd : d.1 + d.2 = T := by omega
  refine ⟨r, hr, d, hd, ?_⟩
  have hone : ∀ i : Fin (d.1 + d.2), ω (p.vertex i.succ) = 1 := hp
  have hsum : ∑ i : Fin (d.1 + d.2), ω (p.vertex i.succ) = (T : ℝ) :=
    calc ∑ i : Fin (d.1 + d.2), ω (p.vertex i.succ)
        = ∑ _i : Fin (d.1 + d.2), (1 : ℝ) := Finset.sum_congr rfl (fun i _ => hone i)
      _ = (T : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hTd]
        simp
  have hle := (excludedStart_le_and_attained ω r d).1 p
  rw [hd] at hle
  linarith

/-! ## One step of the process -/

/-- The two ways a site can enter the next occupied set. -/
private theorem mem_succ_cases (ω : Environment) (T : ℕ) (c₀ : ℝ) (S : Set Lattice)
    (k j : ℕ) (v : Lattice) (hv : v ∈ (augmentedProcess ω T c₀ S k (j + 1)).1) :
    (v ∈ openReachSet (topSites ω) (augmentedProcess ω T c₀ S k j).1 T ∧
      (augmentedProcess ω T c₀ S k j).2 ≤ (augmentedProcess ω T c₀ S k (j + 1)).2) ∨
    (∃ r ∈ (augmentedProcess ω T c₀ S k j).1, IsTriangle ω T c₀ r ∧
      v ∈ triangleTargets T r ∧
      (augmentedProcess ω T c₀ S k (j + 1)).2 = (augmentedProcess ω T c₀ S k j).2 + 1) := by
  simp only [augmentedProcess] at hv ⊢
  split_ifs at hv ⊢ with h
  · rcases hv with hv | hv
    · exact Or.inl ⟨hv, Nat.le_succ _⟩
    · exact Or.inr ⟨_, h.2.1, h.2.2, hv, rfl⟩
  · exact Or.inl ⟨hv, le_rfl⟩

/-! ## Block form of the augmentation step -/

theorem augmentedProcess_subset_levelSet (ω : Environment) (T : ℕ) (c₀ : ℝ)
    (S : Set Lattice) (hS : S ⊆ levelSet 0) (k j : ℕ) :
    (augmentedProcess ω T c₀ S k j).1 ⊆ levelSet ((j : ℤ) * T) := by
  induction j with
  | zero =>
    intro v hv
    have hv' : v ∈ S := by simpa [augmentedProcess] using hv
    have h0 : v.1 + v.2 = 0 := hS hv'
    show v.1 + v.2 = ((0 : ℕ) : ℤ) * (T : ℤ)
    simpa using h0
  | succ j ih =>
    intro v hv
    rcases mem_succ_cases ω T c₀ S k j v hv with ⟨hv1, -⟩ | ⟨r, hr, -, hv2, -⟩
    · have h : v.1 + v.2 = (j : ℤ) * T + T :=
        openReachSet_subset_levelSet (topSites ω) _ ((j : ℤ) * T) T ih hv1
      have e : ((j + 1 : ℕ) : ℤ) * (T : ℤ) = (j : ℤ) * T + T := by push_cast; ring
      show v.1 + v.2 = ((j + 1 : ℕ) : ℤ) * (T : ℤ)
      rw [e, h]
    · have hr' : r.1 + r.2 = (j : ℤ) * T := ih hr
      obtain ⟨h1, -, -⟩ : v.1 + v.2 = r.1 + r.2 + T ∧ r.1 + 1 ≤ v.1 ∧ v.1 ≤ r.1 + T := hv2
      have e : ((j + 1 : ℕ) : ℤ) * (T : ℤ) = (j : ℤ) * T + T := by push_cast; ring
      show v.1 + v.2 = ((j + 1 : ℕ) : ℤ) * (T : ℤ)
      rw [e]
      linarith

theorem augmentedProcess_passage_lower (ω : Environment) (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ)
    (hc₀ : c₀ ≤ 1) (S : Set Lattice) (_hS : S ⊆ levelSet 0) (k j : ℕ) :
    ∀ v ∈ (augmentedProcess ω T c₀ S k j).1, ∃ u ∈ S, ∃ d : ℕ × ℕ,
      u + ((d.1 : ℤ), (d.2 : ℤ)) = v ∧
      (j : ℝ) * T + ((augmentedProcess ω T c₀ S k j).2 : ℝ) * (c₀ - 1) ≤
        lastPassage ω u d - ω u + ω v := by
  clear _hS
  induction j with
  | zero =>
    intro v hv
    have hv' : v ∈ S := by simpa [augmentedProcess] using hv
    refine ⟨v, hv', (0, 0), by ext <;> simp, ?_⟩
    simp [augmentedProcess]
  | succ j ih =>
    intro v hv
    rcases mem_succ_cases ω T c₀ S k j v hv with ⟨hv1, hK⟩ | ⟨r, hr, htri, hv2, hK⟩
    · obtain ⟨r, hrX, e, he, hTe⟩ := open_passage ω T _ v hv1
      obtain ⟨u, hu, d, hd, hb⟩ := ih r hrX
      obtain ⟨d', hd', hb'⟩ := extend_passage ω hd he hb hTe
      refine ⟨u, hu, d', hd', ?_⟩
      have hc : ((augmentedProcess ω T c₀ S k j).2 : ℝ) ≤
          ((augmentedProcess ω T c₀ S k (j + 1)).2 : ℝ) := by exact_mod_cast hK
      have h2 : ((augmentedProcess ω T c₀ S k (j + 1)).2 : ℝ) * (c₀ - 1) ≤
          ((augmentedProcess ω T c₀ S k j).2 : ℝ) * (c₀ - 1) :=
        mul_le_mul_of_nonpos_right hc (by linarith)
      push_cast
      linarith
    · obtain ⟨u, hu, d, hd, hb⟩ := ih r hr
      obtain ⟨e, he, hTe⟩ := triangle_target_passage ω T hT c₀ r htri v hv2
      obtain ⟨d', hd', hb'⟩ := extend_passage ω hd he hb hTe
      refine ⟨u, hu, d', hd', ?_⟩
      rw [hK]
      push_cast
      linarith

end LPPDifferentiability
