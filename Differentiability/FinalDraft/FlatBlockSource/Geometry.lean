/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatBlockSource.Trace
import Mathlib.Tactic

/-! Durrett (1984), Section 9 and Figure 7, in site coordinates. We take
`δ = 1/10` and `L = 20N`; rounding the unit `αN` once gives even lattice
translations and preserves the opposing endpoint orders in each overlap. -/

@[expose] public section

open Set

namespace LPPDifferentiability.FinalDraft.FlatBlockSource

/-- Rotated space coordinate of a first-coordinate trace. -/
def traceRotation (x : ℕ → ℤ) (t : ℕ) : ℤ := 2 * x t - (t : ℤ)

/-- The right parallelogram of Figure 7. Both boundaries are imposed
at every level, including the initial and terminal levels. -/
def RightConfined (N : ℕ) (w : ℤ) (x : ℕ → ℤ) : Prop :=
  ∀ t ≤ 22 * N,
    (w : ℝ) / (N : ℝ) * (t : ℝ) - 3 * w ≤ (traceRotation x t : ℝ) ∧
    (traceRotation x t : ℝ) ≤ (w : ℝ) / (N : ℝ) * (t : ℝ) - w

/-- The event of an actual open crossing of the entire right parallelogram. -/
def RightBlock (N : ℕ) (w : ℤ) (a : Lattice) : Set Environment :=
  {ω | ∃ x, OpenTrace ω a (22 * N) x ∧ RightConfined N w x}

/-- The two reflected parallelogram crossings at a coarse site. -/
def GoodBlock (N : ℕ) (w : ℤ) (a : Lattice) : Set Environment :=
  {ω | (∃ x, OpenTrace ω a (22 * N) x ∧ RightConfined N w x) ∧
    ∃ y, OpenTrace ω a (22 * N) y ∧ RightConfined N w (reflectTrace y)}

/-- The coarse anchor has rotated coordinates `18w(v₁−v₂)`, `20N(v₁+v₂)`. -/
def anchor (N : ℕ) (w : ℤ) (v : ℕ × ℕ) : Lattice :=
  ((10 * (N : ℤ) + 9 * w) * (v.1 : ℤ) + (10 * (N : ℤ) - 9 * w) * (v.2 : ℤ),
    (10 * (N : ℤ) - 9 * w) * (v.1 : ℤ) + (10 * (N : ℤ) + 9 * w) * (v.2 : ℤ))

/-- The time coordinate in Durrett's coarse lattice. -/
theorem anchor_level (N : ℕ) (w : ℤ) (v : ℕ × ℕ) :
    (anchor N w v).1 + (anchor N w v).2 = 20 * (N : ℤ) * ((v.1 : ℤ) + v.2) := by
  simp only [anchor]
  ring

/-- The space coordinate in Durrett's coarse lattice. -/
theorem anchor_rotation (N : ℕ) (w : ℤ) (v : ℕ × ℕ) :
    (anchor N w v).1 - (anchor N w v).2 = 18 * w * ((v.1 : ℤ) - v.2) := by
  simp only [anchor]
  ring

/-- The two coarse steps have the first-coordinate shifts of Figure 7. -/
theorem anchor_step_fst (N : ℕ) (w : ℤ) (u : ℕ × ℕ) :
    (anchor N w (u + (1, 0))).1 = (anchor N w u).1 + (10 * (N : ℤ) + 9 * w) ∧
    (anchor N w (u + (0, 1))).1 = (anchor N w u).1 + (10 * (N : ℤ) - 9 * w) := by
  constructor <;> simp only [anchor, Prod.fst_add, Prod.snd_add, Nat.cast_add,
    Nat.cast_one, add_zero] <;> ring

/-- The all-time confinement bounds at an integer multiple of the scale. -/
theorem RightConfined.at_mul {N : ℕ} {w : ℤ} {x : ℕ → ℤ}
    (hx : RightConfined N w x) (hN : 0 < N) (i : ℕ) (hi : i ≤ 22) :
    ((i : ℤ) - 3) * w ≤ traceRotation x (i * N) ∧
    traceRotation x (i * N) ≤ ((i : ℤ) - 1) * w := by
  have h := hx (i * N) (Nat.mul_le_mul_right N hi)
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hline : (w : ℝ) / (N : ℝ) * ((i * N : ℕ) : ℝ) = (i : ℝ) * w := by
    push_cast
    field_simp [hN']
  rw [hline] at h
  constructor
  · exact_mod_cast (show ((i : ℝ) - 3) * (w : ℝ) ≤ (traceRotation x (i * N) : ℝ) by
      linarith only [h.1])
  · exact_mod_cast (show (traceRotation x (i * N) : ℝ) ≤ ((i : ℝ) - 1) * (w : ℝ) by
      linarith only [h.2])

/-- Reflection negates the rotated coordinate and preserves time. -/
theorem traceRotation_reflect (x : ℕ → ℤ) (t : ℕ) :
    traceRotation (reflectTrace x) t = - traceRotation x t := by
  simp only [traceRotation, reflectTrace]
  omega

/-- The reflected crossings of one block have a common vertex by level `4N`. -/
theorem crossings_meet {ω : Environment} {a : Lattice} {N : ℕ} {w : ℤ} (hN : 0 < N)
    (hw : 0 ≤ w) {x y : ℕ → ℤ}
    (hx : OpenTrace ω a (22 * N) x) (hy : OpenTrace ω a (22 * N) y)
    (hX : RightConfined N w x) (hY : RightConfined N w (reflectTrace y)) :
    ∃ s ≤ 4 * N, x s = y s := by
  have hx₀ := hX.at_mul hN 0 (by decide)
  have hy₀ := hY.at_mul hN 0 (by decide)
  have hx₄ := hX.at_mul hN 4 (by decide)
  have hy₄ := hY.at_mul hN 4 (by decide)
  rw [traceRotation_reflect] at hy₀ hy₄
  norm_num [traceRotation] at hx₀ hy₀ hx₄ hy₄
  have hs : (0 : ℤ) + x (0 : ℕ) ≤ 0 + y (0 : ℕ) := by omega
  have he : (0 : ℤ) + y (0 + 4 * N) ≤ 0 + x (0 + 4 * N) := by
    simp only [zero_add]
    omega
  obtain ⟨j, hj, heq⟩ := traces_meet hx.1 hy.1 (by omega) (by omega) hs he
  exact ⟨j, hj, by simpa only [zero_add] using heq⟩

/-- The outgoing tails in the first block are reachable from one initial seed. -/
theorem reaches_first_tails {ω : Environment} {a : Lattice} {N : ℕ} {w : ℤ}
    (hN : 0 < N) (hw : 0 ≤ w) {x y : ℕ → ℤ}
    (hx : OpenTrace ω a (22 * N) x) (hy : OpenTrace ω a (22 * N) y)
    (hX : RightConfined N w x) (hY : RightConfined N w (reflectTrace y)) :
    ∀ t, 4 * N ≤ t → t ≤ 22 * N →
      traceSite a t (x t) ∈ openReachSet (topSites ω) {traceSite a 0 (x 0)} t ∧
      traceSite a t (y t) ∈ openReachSet (topSites ω) {traceSite a 0 (x 0)} t := by
  obtain ⟨s, hs, hxy⟩ := crossings_meet hN hw hx hy hX hY
  have hstart : traceSite a 0 (x 0) ∈ openReachSet (topSites ω) {traceSite a 0 (x 0)} (0 + 0) := by
    simp [openReachSet_zero]
  have hmeet := hx.extendReach (m := 0) (show 0 ≤ s by omega) (show s ≤ 22 * N by omega) hstart
  intro t ht hT
  constructor
  · simpa only [zero_add] using hx.extendReach (m := 0) (show 0 ≤ t by omega) hT hstart
  · rw [hxy] at hmeet
    simpa only [zero_add] using hy.extendReach (hs.trans ht) hT hmeet

/-- In the overlap, contact before the new crossings' common vertex
gives access to both tails. The endpoint orders may put the old trace
on either side of that vertex. -/
private theorem reaches_new_tails_of_orders {ω : Environment} {a b : Lattice} {N m : ℕ}
    {x X Y : ℕ → ℤ} {S : Set Lattice}
    (hx : OpenTrace ω a (22 * N) x) (hX : OpenTrace ω b (22 * N) X)
    (hY : OpenTrace ω b (22 * N) Y)
    (hlevel : b.1 + b.2 = a.1 + a.2 + (20 * N : ℕ))
    (hstartX : b.1 + X 0 ≤ a.1 + x (20 * N)) (hstartY : a.1 + x (20 * N) ≤ b.1 + Y 0)
    (hend : b.1 + Y (2 * N) ≤ a.1 + x (22 * N) ∨
      a.1 + x (22 * N) ≤ b.1 + X (2 * N))
    (hmeet : ∃ s ≤ 4 * N, X s = Y s)
    (hold : ∀ t, 4 * N ≤ t → t ≤ 22 * N →
      traceSite a t (x t) ∈ openReachSet (topSites ω) S (m + t)) :
    ∀ t, 4 * N ≤ t → t ≤ 22 * N →
      traceSite b t (X t) ∈ openReachSet (topSites ω) S (m + 20 * N + t) ∧
      traceSite b t (Y t) ∈ openReachSet (topSites ω) S (m + 20 * N + t) := by
  obtain ⟨s, hs, hXY⟩ := hmeet
  have htransfer {Z : ℕ → ℤ} {j : ℕ} (hj : j ≤ 2 * N)
      (he : a.1 + x (20 * N + j) = b.1 + Z j) :
      traceSite b j (Z j) ∈ openReachSet (topSites ω) S (m + 20 * N + j) := by
    have heq : traceSite a (20 * N + j) (x (20 * N + j)) = traceSite b j (Z j) :=
      traceSite_eq_of_level_fst (by push_cast; omega) he
    have hr := hold (20 * N + j) (by omega) (by omega)
    rw [heq, ← Nat.add_assoc] at hr
    exact hr
  have hcontact : (∃ j ≤ s, traceSite b j (X j) ∈ openReachSet (topSites ω) S (m + 20 * N + j)) ∨
      (∃ j ≤ s, traceSite b j (Y j) ∈ openReachSet (topSites ω) S (m + 20 * N + j)) := by
    by_cases hs2 : s ≤ 2 * N
    · by_cases horder : a.1 + x (20 * N + s) ≤ b.1 + X s
      · have hEnd : a.1 + x (20 * N + s) ≤ b.1 + X (0 + s) := by simpa using horder
        obtain ⟨j, hj, he⟩ := traces_meet hX.1 hx.1 (by omega) (by omega) hstartX hEnd
        exact Or.inl ⟨j, hj, htransfer (hj.trans hs2) (by simpa only [zero_add] using he.symm)⟩
      · have hEnd : b.1 + Y (0 + s) ≤ a.1 + x (20 * N + s) := by
          rw [zero_add, ← hXY]
          exact (lt_of_not_ge horder).le
        obtain ⟨j, hj, he⟩ := traces_meet hx.1 hY.1 (by omega) (by omega) hstartY hEnd
        exact Or.inr ⟨j, hj, htransfer (hj.trans hs2) (by simpa only [zero_add] using he)⟩
    · rcases hend with hend | hend
      · have hEnd : b.1 + Y (0 + 2 * N) ≤ a.1 + x (20 * N + 2 * N) := by
          simpa only [zero_add, show 20 * N + 2 * N = 22 * N by omega] using hend
        obtain ⟨j, hj, he⟩ := traces_meet hx.1 hY.1 (by omega) (by omega) hstartY hEnd
        exact Or.inr ⟨j, by omega, htransfer hj (by simpa only [zero_add] using he)⟩
      · have hEnd : a.1 + x (20 * N + 2 * N) ≤ b.1 + X (0 + 2 * N) := by
          simpa only [zero_add, show 20 * N + 2 * N = 22 * N by omega] using hend
        obtain ⟨j, hj, he⟩ := traces_meet hX.1 hx.1 (by omega) (by omega) hstartX hEnd
        exact Or.inl ⟨j, by omega, htransfer hj (by simpa only [zero_add] using he.symm)⟩
  have hr : traceSite b s (X s) ∈ openReachSet (topSites ω) S (m + 20 * N + s) := by
    rcases hcontact with ⟨j, hj, h⟩ | ⟨j, hj, h⟩
    · exact hX.extendReach hj (by omega) h
    · rw [hXY]
      exact hY.extendReach hj (by omega) h
  intro t ht hT
  exact ⟨hX.extendReach (hs.trans ht) hT hr, hY.extendReach (hs.trans ht) hT (hXY ▸ hr)⟩

/-- The two Figure 7 overlaps transmit physical reachability to both
outgoing tails in the next coarse block. -/
theorem reaches_next_tails {ω : Environment} {a b : Lattice} {N m : ℕ} {w : ℤ}
    (hN : 0 < N) (hw : 0 ≤ w) {S : Set Lattice} {x y X Y : ℕ → ℤ}
    (hx : OpenTrace ω a (22 * N) x) (hy : OpenTrace ω a (22 * N) y)
    (hxc : RightConfined N w x) (hyc : RightConfined N w (reflectTrace y))
    (hX : OpenTrace ω b (22 * N) X) (hY : OpenTrace ω b (22 * N) Y)
    (hXc : RightConfined N w X) (hYc : RightConfined N w (reflectTrace Y))
    (hlevel : b.1 + b.2 = a.1 + a.2 + (20 * N : ℕ))
    (hfst : b.1 = a.1 + (10 * (N : ℤ) + 9 * w) ∨ b.1 = a.1 + (10 * (N : ℤ) - 9 * w))
    (hold : ∀ t, 4 * N ≤ t → t ≤ 22 * N →
      traceSite a t (x t) ∈ openReachSet (topSites ω) S (m + t) ∧
      traceSite a t (y t) ∈ openReachSet (topSites ω) S (m + t)) :
    ∀ t, 4 * N ≤ t → t ≤ 22 * N →
      traceSite b t (X t) ∈ openReachSet (topSites ω) S (m + 20 * N + t) ∧
      traceSite b t (Y t) ∈ openReachSet (topSites ω) S (m + 20 * N + t) := by
  have hX₀ := hXc.at_mul hN 0 (by decide)
  have hX₂ := hXc.at_mul hN 2 (by decide)
  have hY₀ := hYc.at_mul hN 0 (by decide)
  have hY₂ := hYc.at_mul hN 2 (by decide)
  rw [traceRotation_reflect] at hY₀ hY₂
  rcases hfst with hr | hl
  · have h20 := hxc.at_mul hN 20 (by decide)
    have h22 := hxc.at_mul hN 22 (by decide)
    norm_num [traceRotation] at hX₀ hY₀ hY₂ h20 h22
    exact reaches_new_tails_of_orders hx hX hY hlevel (by omega) (by omega)
      (Or.inl (by omega)) (crossings_meet hN hw hX hY hXc hYc)
      (fun t ht hT => (hold t ht hT).1)
  · have h20 := hyc.at_mul hN 20 (by decide)
    have h22 := hyc.at_mul hN 22 (by decide)
    rw [traceRotation_reflect] at h20 h22
    norm_num [traceRotation] at hX₀ hX₂ hY₀ h20 h22
    exact reaches_new_tails_of_orders hy hX hY hlevel (by omega) (by omega)
      (Or.inr (by omega)) (crossings_meet hN hw hX hY hXc hYc)
      (fun t ht hT => (hold t ht hT).2)

end LPPDifferentiability.FinalDraft.FlatBlockSource
