/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.BoundarySupportMeans
public import Busemann.Frozen.Definitions.Recovery
public import Busemann.Frozen.Definitions.Additive
import Busemann.Geometry.SupportOrder
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic

/-! Pointwise order and finite rectangles for the boundary-cocycle argument
of GRS arXiv:1510.00860v1, Lemma 5.1. All rectangles are finite. -/

@[expose] public section
open LPPDifferentiability Filter
open scoped BigOperators NNReal Topology

namespace LPP.Busemann

/-- Weak tilt order, including equal first coordinates, bounds both signs by
one comparison field. This retains the source's within-tilt and strict order. -/
theorem native_unit_bounds_of_order
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (M P : SupportTilt g → Lattice → Lattice → ℝ)
    (hWithin : ∀ h x, P h x (x + (1, 0)) ≤ M h x (x + (1, 0)) ∧
      M h x (x + (0, 1)) ≤ P h x (x + (0, 1)))
    (hCross : ∀ h k, h.1.1 < k.1.1 → ∀ x,
      M k x (x + (1, 0)) ≤ P h x (x + (1, 0)) ∧
      P h x (x + (0, 1)) ≤ M k x (x + (0, 1)))
    (h k : SupportTilt g) (hhk : h.1.1 ≤ k.1.1) (x : Lattice) :
    M k x (x + (1, 0)) ≤ M h x (x + (1, 0)) ∧
      P k x (x + (1, 0)) ≤ M h x (x + (1, 0)) ∧
      M h x (x + (0, 1)) ≤ P k x (x + (0, 1)) ∧
      P h x (x + (0, 1)) ≤ P k x (x + (0, 1)) := by
  rcases lt_or_eq_of_le hhk with hlt | heq
  · have hc := hCross h k hlt x
    exact ⟨hc.1.trans (hWithin h x).1,
      (hWithin k x).1.trans (hc.1.trans (hWithin h x).1),
      (hWithin h x).2.trans (hc.2.trans (hWithin k x).2),
      hc.2.trans (hWithin k x).2⟩
  · have hsame : h = k := (supportTilt_coordinate_order g hhom h k).2 heq
    subst k
    exact ⟨le_rfl, (hWithin h x).1, (hWithin h x).2, le_rfl⟩

/-- A lower bound and cofinal upper comparisons extend the countable
longitudinal limits to an arbitrary parameter sequence in the source argument. -/
theorem tendsto_of_eventual_upper_comparisons
    (f a : ℕ → ℝ) (w : ℝ) (hLower : ∀ n, w ≤ f n)
    (hLimit : Tendsto a atTop (𝓝 w))
    (hUpper : ∀ k, ∀ᶠ n in atTop, f n ≤ a k) :
    Tendsto f atTop (𝓝 w) := by
  apply tendsto_order.mpr
  constructor
  · intro l hl
    exact Eventually.of_forall fun n => hl.trans_le (hLower n)
  · intro u hu
    obtain ⟨k, hk⟩ := (hLimit.eventually (Iio_mem_nhds hu)).exists
    exact (hUpper k).mono fun n hn => hn.trans_lt hk

private theorem cocycle_cell
    (C : Lattice → Lattice → ℝ) (hC : is_additive C)
    (x u v : Lattice) :
    C x (x + v) = C x (x + u) - C (x + v) (x + v + u) +
      C (x + u) (x + u + v) := by
  have h1 := hC x (x + u) (x + u + v)
  have h2 := hC x (x + v) (x + v + u)
  have heq : x + u + v = x + v + u := by abel
  rw [heq] at h1 ⊢
  linarith only [h1, h2]

/-- Additivity telescopes a finite cocycle rectangle, before any boundary
limit is taken. This avoids subtraction of infinite boundary values. -/
theorem cocycle_finite_rectangle
    (C : Lattice → Lattice → ℝ) (hC : is_additive C)
    (x u v : Lattice) (n : ℕ) :
    C x (x + v) =
      (∑ j ∈ Finset.range n,
        (C (x + j • u) (x + j • u + u) -
          C (x + j • u + v) (x + j • u + v + u))) +
        C (x + n • u) (x + n • u + v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : x + (n + 1) • u = x + n • u + u := by rw [succ_nsmul]; abel
    rw [Finset.sum_range_succ, hstep]
    have hcell := cocycle_cell C hC (x + n • u) u v
    linarith only [ih, hcell]

private theorem shifted_sum_identity
    (ω : Lattice → ℝ) (x u v : Lattice) (n : ℕ) :
    (∑ j ∈ Finset.range n, (ω (x + j • u) - ω (x + j • u + v))) +
        ω (x + n • u) =
      ω x + ∑ j ∈ Finset.range n,
        (ω (x + (j + 1) • u) - ω (x + j • u + v)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith only [ih]

/-- Longitudinal limits, recovery on the terminal side, and the exact shifted
adjacent-axis sums force the transverse edge to positive infinity. This is
the finite-rectangle step in GRS arXiv:1510.00860v1, Lemma 5.1. -/
theorem transverse_tendsto_atTop_of_longitudinal
    (ω : Lattice → ℝ) (B : ℕ → Lattice → Lattice → ℝ)
    (u v : Lattice) (hAdd : ∀ k, is_additive (B k))
    (hLower : ∀ k x, ω x ≤ B k x (x + v))
    (hLong : ∀ x, Tendsto (fun k => B k x (x + u)) atTop (𝓝 (ω x)))
    (hWalk : ∀ x : Lattice, ∀ K : ℝ, ∃ n : ℕ,
      K < ∑ j ∈ Finset.range n,
        (ω (x + (j + 1) • u) - ω (x + j • u + v))) :
    ∀ x : Lattice, Tendsto (fun k => B k x (x + v)) atTop atTop := by
  intro x
  apply tendsto_atTop.mpr
  intro K
  obtain ⟨n, hn⟩ := hWalk x (K - ω x)
  let A (k : ℕ) : ℝ :=
    (∑ j ∈ Finset.range n,
      (B k (x + j • u) (x + j • u + u) -
        B k (x + j • u + v) (x + j • u + v + u))) + ω (x + n • u)
  have hBound (k : ℕ) : A k ≤ B k x (x + v) := by
    rw [cocycle_finite_rectangle (B k) (hAdd k) x u v n]
    have hl := hLower k (x + n • u)
    dsimp only [A]
    linarith only [hl]
  have hLimit : Tendsto A atTop
      (𝓝 (ω x + ∑ j ∈ Finset.range n,
        (ω (x + (j + 1) • u) - ω (x + j • u + v)))) := by
    rw [← shifted_sum_identity ω x u v n]
    have hSum := tendsto_finsetSum (Finset.range n) fun j _ =>
      (hLong (x + j • u)).sub (hLong (x + j • u + v))
    simpa only [A] using hSum.add_const (ω (x + n • u))
  have hLarge : K < ω x + ∑ j ∈ Finset.range n,
      (ω (x + (j + 1) • u) - ω (x + j • u + v)) := by linarith only [hn]
  filter_upwards [hLimit.eventually (Ioi_mem_nhds hLarge)] with k hk
  exact (le_of_lt hk).trans (hBound k)

end LPP.Busemann
