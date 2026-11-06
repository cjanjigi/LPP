/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.OrientedPercolation
public import LPP_Foundations.Model.Paths.HorizontalFirst
public import LPP_Foundations.Model.Paths.Level
public import LPP_Foundations.Frozen.Model.LastPassage
import LPP_Foundations.Model.LastPassage.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith

/-!
# Triangle geometry for the flat-segment branch

The deterministic statements for the triangle argument in the flat-segment case. Open paths cannot
reach to the left of a triangle, the target block is a translate of the antidiagonal block, each
target is reached from the corner with the stated passage bound, and the triangle property depends
only on the weights on the levels above the corner, up to the triangle height.
-/

@[expose] public section

namespace LPPDifferentiability

open Finset

/-- The weight of the horizontal-first path, written as a sum over its local times. -/
private theorem horizontalFirst_weight (ω : Environment) (r : Lattice) (a b : ℕ) :
    pathWeight ω (horizontalFirst r (a, b)) =
      ∑ k ∈ range (a + b), ω (r.1 + ((min k a : ℕ) : ℤ), r.2 + ((k - a : ℕ) : ℤ)) := by
  unfold pathWeight
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

/-- A lower bound for a sum when every term after the first is `1`. -/
private theorem shift_sum_lower (f : ℕ → ℝ) (c : ℝ) (hf1 : c ≤ f 1) :
    ∀ n : ℕ, (∀ k : ℕ, 2 ≤ k → k ≤ n + 1 → f k = 1) →
      c + (n : ℝ) ≤ (∑ k ∈ range n, f (k + 1)) + f (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro _
    simpa using hf1
  | succ n ih =>
    intro h
    have h' := ih (fun k hk1 hk2 => h k hk1 (by omega))
    have h2 := h (n + 1 + 1) (by omega) (by omega)
    rw [Finset.sum_range_succ]
    push_cast
    linarith

/-- The passage bound from the corner to the target `r + (a, b)`, along the horizontal-first
path. -/
private theorem passage_core (ω : Environment) (r : Lattice) (c₀ : ℝ) (m a b : ℕ)
    (ha1 : 1 ≤ a) (hab : a + b = m + 1) (hr : IsTriangle ω (m + 1) c₀ r) :
    ((m + 1 : ℕ) : ℝ) + c₀ - 1 ≤
      lastPassage ω r (a, b) - ω r + ω (r + ((a : ℤ), (b : ℤ))) := by
  unfold IsTriangle at hr
  obtain ⟨hc1, hc2, hc3⟩ := hr
  have hf1 : c₀ ≤ ω (r.1 + ((min 1 a : ℕ) : ℤ), r.2 + (((1 : ℕ) - a : ℕ) : ℤ)) := by
    have e1 : ω (r.1 + ((min 1 a : ℕ) : ℤ), r.2 + (((1 : ℕ) - a : ℕ) : ℤ)) =
        ω (r.1 + 1, r.2) := by
      congr 1
      exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)
    rw [e1]
    exact hc2.1
  have hV : ∀ k : ℕ, 2 ≤ k → k ≤ m + 1 →
      ω (r.1 + ((min k a : ℕ) : ℤ), r.2 + ((k - a : ℕ) : ℤ)) = 1 := by
    intro k hk1 hk2
    apply hc3 (r.1 + ((min k a : ℕ) : ℤ), r.2 + ((k - a : ℕ) : ℤ))
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
    · intro h
      have h3 := congrArg (fun p : Lattice => p.1 + p.2) h
      dsimp only at h3
      omega
  have hsh : c₀ + (m : ℝ) ≤
      (∑ k ∈ range m, ω (r.1 + ((min (k + 1) a : ℕ) : ℤ), r.2 + (((k + 1) - a : ℕ) : ℤ))) +
        ω (r.1 + ((min (m + 1) a : ℕ) : ℤ), r.2 + (((m + 1) - a : ℕ) : ℤ)) :=
    shift_sum_lower (fun k => ω (r.1 + ((min k a : ℕ) : ℤ), r.2 + ((k - a : ℕ) : ℤ)))
      c₀ hf1 m hV
  have hlp := pathWeight_le_lastPassage ω (horizontalFirst r (a, b))
  rw [horizontalFirst_weight, hab, Finset.sum_range_succ'] at hlp
  have e0 : ω (r.1 + ((min 0 a : ℕ) : ℤ), r.2 + (((0 : ℕ) - a : ℕ) : ℤ)) = ω r := by
    congr 1
    exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)
  have eT : ω (r.1 + ((min (m + 1) a : ℕ) : ℤ), r.2 + (((m + 1) - a : ℕ) : ℤ)) =
      ω (r + ((a : ℤ), (b : ℤ))) := by
    congr 1
    exact Prod.ext (by simp only [Prod.fst_add]; omega) (by simp only [Prod.snd_add]; omega)
  push_cast
  linarith [hsh, hlp, e0, eT]

/-- Open paths from the sites on level `r₁ + r₂` (weakly left of `r₁`) cannot reach the
column `r₁` or any column to its right, because the triangle closes those sites. -/
theorem openReachSet_left_of_triangle (ω : Environment) (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ)
    (r : Lattice) (hr : IsTriangle ω T c₀ r) (X : Set Lattice)
    (hX : ∀ x ∈ X, x.1 + x.2 = r.1 + r.2 ∧ x.1 ≤ r.1) :
    ∀ v ∈ openReachSet (topSites ω) X T, v.1 ≤ r.1 - 1 := by
  intro v hv
  obtain ⟨u, hu, hpath, hlev⟩ := hv
  obtain ⟨hul, hua⟩ := hX u hu
  obtain ⟨d, hd, p, hO⟩ := hpath
  unfold IsTriangle at hr
  obtain ⟨hc1, hc2, -⟩ := hr
  have hv1 : v.1 = u.1 + (d.1 : ℤ) := by subst hd; simp
  have hv2 : v.2 = u.2 + (d.2 : ℤ) := by subst hd; simp
  have hTd : d.1 + d.2 = T := by omega
  have key : ∀ i : Fin (d.1 + d.2 + 1), 1 ≤ i.val → (p.vertex i).1 ≤ r.1 - 1 := by
    intro i
    induction i using Fin.induction with
    | zero =>
      intro h
      simp at h
    | succ j ih =>
      intro _
      have hjlt : j.val < d.1 + d.2 := j.isLt
      have hy : ω (p.vertex j.succ) = 1 := hO j
      have hly := p.level j.succ
      simp only [Fin.val_succ] at hly
      have hstep : ((p.vertex j.succ).1 = (p.vertex j.castSucc).1 + 1 ∧
          (p.vertex j.succ).2 = (p.vertex j.castSucc).2) ∨
          ((p.vertex j.succ).1 = (p.vertex j.castSucc).1 ∧
          (p.vertex j.succ).2 = (p.vertex j.castSucc).2 + 1) := by
        rcases p.step j with h | h
        · left
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          simp only [Prod.fst_add, Prod.snd_add] at h1 h2
          exact ⟨by omega, by omega⟩
        · right
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          simp only [Prod.fst_add, Prod.snd_add] at h1 h2
          exact ⟨by omega, by omega⟩
      by_cases hj : j.val = 0
      · have hx : p.vertex j.castSucc = u := by
          rw [show j.castSucc = 0 from Fin.ext (by simp [hj]), p.start]
        rw [hx] at hstep
        by_contra hc
        rcases (show (p.vertex j.succ).1 = r.1 ∨ (p.vertex j.succ).1 = r.1 + 1 by omega)
          with h | h
        · have hyv : p.vertex j.succ = (r.1, r.2 + 1) :=
            Prod.ext (by dsimp only; omega) (by dsimp only; omega)
          rw [hyv] at hy
          have hc1' := hc1 1 le_rfl hT
          push_cast at hc1'
          linarith
        · have hyv : p.vertex j.succ = (r.1 + 1, r.2) :=
            Prod.ext (by dsimp only; omega) (by dsimp only; omega)
          rw [hyv] at hy
          linarith [hc2.2]
      · have hxle := ih (by simp only [Fin.val_castSucc]; omega)
        by_contra hc
        have hyv : p.vertex j.succ = (r.1, r.2 + ((j.val + 1 : ℕ) : ℤ)) :=
          Prod.ext (by dsimp only; omega) (by dsimp only; omega)
        have hcl := hc1 (j.val + 1) (by omega) (by omega)
        rw [hyv] at hy
        linarith
  have hlast := key (Fin.last (d.1 + d.2)) (by simp only [Fin.val_last]; omega)
  rw [p.finish, hd] at hlast
  exact hlast

/-- The target block of a triangle is a translate of the antidiagonal right block. -/
theorem triangleTargets_eq (T : ℕ) (r : Lattice) :
    triangleTargets T r = (fun z => (r.1, r.2 + T) + z) '' antidiagRightBlock T := by
  ext z
  constructor
  · intro hz
    obtain ⟨hz1, hz2, hz3⟩ : z.1 + z.2 = r.1 + r.2 + T ∧ r.1 + 1 ≤ z.1 ∧ z.1 ≤ r.1 + T := hz
    have hmem : (z.1 - r.1) + (z.2 - (r.2 + T)) = 0 ∧ 1 ≤ z.1 - r.1 ∧
        z.1 - r.1 ≤ (T : ℤ) := ⟨by omega, by omega, by omega⟩
    refine ⟨(z.1 - r.1, z.2 - (r.2 + T)), hmem, ?_⟩
    refine Prod.ext ?_ ?_
    · show r.1 + (z.1 - r.1) = z.1
      omega
    · show r.2 + T + (z.2 - (r.2 + T)) = z.2
      omega
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx1, hx2, hx3⟩ : x.1 + x.2 = 0 ∧ 1 ≤ x.1 ∧ x.1 ≤ (T : ℤ) := hx
    have hmem : r.1 + x.1 + (r.2 + T + x.2) = r.1 + r.2 + T ∧ r.1 + 1 ≤ r.1 + x.1 ∧
        r.1 + x.1 ≤ r.1 + T := ⟨by omega, by omega, by omega⟩
    exact hmem

/-- The passage from the corner `r` to each target: a monotone path from `r` whose weight,
with the start removed and the target added, is at least `T + c₀ - 1`. -/
theorem triangle_target_passage (ω : Environment) (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ)
    (r : Lattice) (hr : IsTriangle ω T c₀ r) :
    ∀ w ∈ triangleTargets T r, ∃ d : ℕ × ℕ, r + ((d.1 : ℤ), (d.2 : ℤ)) = w ∧
      (T : ℝ) + c₀ - 1 ≤ lastPassage ω r d - ω r + ω w := by
  intro w hw
  obtain ⟨hwl, hwa, hwb⟩ : w.1 + w.2 = r.1 + r.2 + T ∧ r.1 + 1 ≤ w.1 ∧ w.1 ≤ r.1 + T := hw
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = w.1 - r.1 :=
    ⟨(w.1 - r.1).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = w.2 - r.2 :=
    ⟨(w.2 - r.2).toNat, Int.toNat_of_nonneg (by omega)⟩
  have ha1 : 1 ≤ a := by omega
  have hab : a + b = T := by omega
  have hwd : w = r + ((a : ℤ), (b : ℤ)) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]; omega
    · simp only [Prod.snd_add]; omega
  refine ⟨(a, b), hwd.symm, ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, T = m + 1 := ⟨T - 1, by omega⟩
  rw [hwd]
  exact passage_core ω r c₀ m a b ha1 hab hr

/-- The triangle property at `r` for the environment `ω` is the same as for `ω'` when the
two environments agree on the levels `r₁ + r₂ + 1` to `r₁ + r₂ + T`. -/
private theorem isTriangle_of_agree (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ) (r : Lattice)
    (ω ω' : Environment)
    (h : ∀ z : Lattice, r.1 + r.2 < z.1 + z.2 → z.1 + z.2 ≤ r.1 + r.2 + T → ω z = ω' z)
    (hr : IsTriangle ω T c₀ r) : IsTriangle ω' T c₀ r := by
  unfold IsTriangle at hr ⊢
  obtain ⟨hc1, hc2, hc3⟩ := hr
  refine ⟨?_, ?_, ?_⟩
  · intro i hi1 hi2
    rw [← h (r.1, r.2 + i) (by dsimp only; omega) (by dsimp only; omega)]
    exact hc1 i hi1 hi2
  · rw [← h (r.1 + 1, r.2) (by dsimp only; omega) (by dsimp only; omega)]
    exact hc2
  · intro z hz1 hz2 hz3 hz4
    rw [← h z (by omega) (by omega)]
    exact hc3 z hz1 hz2 hz3 hz4

/-- Whether a site is a triangle depends only on the weights on the levels above the corner,
up to the triangle height `T`, provided `T ≥ 1`. -/
theorem isTriangle_local (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ) (r : Lattice) (ω ω' : Environment)
    (h : ∀ z : Lattice, r.1 + r.2 < z.1 + z.2 → z.1 + z.2 ≤ r.1 + r.2 + T → ω z = ω' z) :
    IsTriangle ω T c₀ r ↔ IsTriangle ω' T c₀ r :=
  ⟨isTriangle_of_agree T hT c₀ r ω ω' h,
    isTriangle_of_agree T hT c₀ r ω' ω (fun z h1 h2 => (h z h1 h2).symm)⟩

end LPPDifferentiability
