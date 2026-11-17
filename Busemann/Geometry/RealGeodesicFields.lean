/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.GeodesicPassageDifferenceERealLimit
public import Busemann.Geometry.GeodesicPassageDifferenceLimit
public import Busemann.Frozen.Definitions.Additive
public import LPP_Foundations.Model.LastPassage.PassageDifferenceLimits
public import LPP_Foundations.Model.LastPassage.GeodesicSegments
import Busemann.Geometry.GeodesicCocycleFiniteness
import Busemann.Geometry.GeodesicCocycleLimitAlgebra
import Mathlib.Topology.Instances.EReal.Lemmas

@[expose] public section
open Filter LPPDifferentiability
open scoped Topology
namespace LPP.Busemann

/-- Internal deterministic bridge: the actual neighboring-start upper bounds
along one ordinary signed-root maximizing ray force a unique additive real
pair field with passage-difference limits at every common valid entry.
The bound premise is the conclusion of the separate original-law full-event
producer and must be discharged when this lemma is applied. Strong Existence,
g406/g408a/g609, lines 1596–1693. Recovery and calibration are separate. -/
theorem exists_unique_real_geodesic_pair_field_of_neighbor_bounds
    (ω : LPPDifferentiability.Environment)
    (u : LPPDifferentiability.Lattice)
    (γ : ℕ → LPPDifferentiability.Lattice)
    (hstart : γ 0 = u)
    (hsteps : ∀ n : ℕ,
      γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
        γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ)))
    (hsegments : has_maximizing_segments ω γ)
    (hescape₁ : Tendsto (fun n : ℕ => (γ n).1) atTop atTop)
    (hescape₂ : Tendsto (fun n : ℕ => (γ n).2) atTop atTop)
    (hNeighborBounds : ∀ x : Lattice, ∃ (N : ℕ) (K : ℝ),
      x ≤ γ N ∧
      x + ((1 : ℤ), (0 : ℤ)) ≤ γ N ∧
      x + ((0 : ℤ), (1 : ℤ)) ≤ γ N ∧
      ∀ n : ℕ,
        (lastPassage ω x
            (((γ (N + n)).1 - x.1).toNat, ((γ (N + n)).2 - x.2).toNat) -
          lastPassage ω (x + ((1 : ℤ), (0 : ℤ)))
            (((γ (N + n)).1 - (x + ((1 : ℤ), (0 : ℤ))).1).toNat,
             ((γ (N + n)).2 - (x + ((1 : ℤ), (0 : ℤ))).2).toNat) ≤ K) ∧
        (lastPassage ω x
            (((γ (N + n)).1 - x.1).toNat, ((γ (N + n)).2 - x.2).toNat) -
          lastPassage ω (x + ((0 : ℤ), (1 : ℤ)))
            (((γ (N + n)).1 - (x + ((0 : ℤ), (1 : ℤ))).1).toNat,
             ((γ (N + n)).2 - (x + ((0 : ℤ), (1 : ℤ))).2).toNat) ≤ K)) :
    ∃! C : Lattice → Lattice → ℝ,
      has_passage_difference_limits ω γ C ∧
      is_additive C := by
  classical
  have hsegmentsOld := (has_maximizing_segments_iff ω γ).mp hsegments
  -- Obtain the all-site extended-real limits from the actual maximizing ray.
  have hEReal := exists_unique_geodesic_passage_difference_ereal_limit
    ω u γ hstart hsteps hsegmentsOld hescape₁ hescape₂
  have hQuadrant := exists_unique_quadrant_geodesic_passage_difference_limit
    ω u γ hstart hsteps hsegmentsOld hescape₁ hescape₂
  let bE : Lattice → EReal := fun x => Classical.choose (hEReal x).exists
  have hbE (x : Lattice) :
      (⊥ : EReal) < bE x ∧ ∀ N : ℕ, x ≤ γ N →
        let f : ℕ → ℝ := fun n =>
          lastPassage ω x
            (((γ (N + n)).1 - x.1).toNat, ((γ (N + n)).2 - x.2).toNat) -
          lastPassage ω u
            (((γ (N + n)).1 - u.1).toNat, ((γ (N + n)).2 - u.2).toNat)
        Monotone f ∧ Tendsto (fun n : ℕ => (f n : EReal)) atTop (𝓝 (bE x)) ∧
          (f 0 : EReal) ≤ bE x := by
    simpa only [bE] using Classical.choose_spec (hEReal x).exists
  -- Use one local root-relative sequence for all later comparisons.
  let rootRelative (x : Lattice) (N : ℕ) : ℕ → ℝ := fun n =>
    lastPassage ω x
      (((γ (N + n)).1 - x.1).toNat, ((γ (N + n)).2 - x.2).toNat) -
    lastPassage ω u
      (((γ (N + n)).1 - u.1).toNat, ((γ (N + n)).2 - u.2).toNat)
  have hRootE (x : Lattice) (N : ℕ) (hN : x ≤ γ N) :
      Tendsto (fun n : ℕ => (rootRelative x N n : EReal)) atTop (𝓝 (bE x)) := by
    have hEntry := (hbE x).2 N hN
    have hLimit := hEntry.2.1
    simpa only [rootRelative] using hLimit
  -- Northeast finite limits identify the same EReal values by uniqueness.
  have hNortheastTop (x : Lattice) (hux : u ≤ x) : bE x < (⊤ : EReal) := by
    obtain ⟨c, hc, _hunique⟩ := hQuadrant x hux
    obtain ⟨N, _K, hN, _hEast, _hNorth, _hBounds⟩ := hNeighborBounds x
    have hRealLimit : Tendsto (rootRelative x N) atTop (𝓝 c) := by
      have hEntry := hc N hN
      simpa only [rootRelative] using hEntry.2.1
    have hRealERealLimit :
        Tendsto (fun n : ℕ => (rootRelative x N n : EReal)) atTop
          (𝓝 (c : EReal)) :=
      (continuous_coe_real_ereal.tendsto c).comp hRealLimit
    have hValue : bE x = (c : EReal) :=
      tendsto_nhds_unique (hRootE x N hN) hRealERealLimit
    rw [hValue]
    exact EReal.coe_lt_top c
  -- A common valid tail turns a neighbor bound into a real upper increment.
  have hNoTopFromNeighbor
      (y x : Lattice) (N : ℕ) (K : ℝ)
      (hy : y ≤ γ N) (hx : x ≤ γ N)
      (hbound : ∀ n : ℕ, rootRelative y N n - rootRelative x N n ≤ K)
      (hfiniteX : bE x < (⊤ : EReal)) :
      bE y < (⊤ : EReal) := by
    let f : ℕ → ℝ := rootRelative y N
    let g : ℕ → ℝ := rootRelative x N
    have hrealBound (n : ℕ) : f n ≤ K + g n := by
      dsimp only [f, g]
      linarith [hbound n]
    exact ereal_limit_finite_of_eventual_real_upper_increment
      f g (bE y) (bE x) K
      (by simpa only [f] using hRootE y N hy)
      (by simpa only [g] using hRootE x N hx)
      (hbE x).1 hfiniteX (Filter.Eventually.of_forall hrealBound)
  -- The west predecessor is covered at the same N as its east neighbor.
  have hWestTop (x : Lattice) (hfiniteX : bE x < (⊤ : EReal)) :
      bE (x - ((1 : ℤ), (0 : ℤ))) < (⊤ : EReal) := by
    let y := x - ((1 : ℤ), (0 : ℤ))
    have hyEast : y + ((1 : ℤ), (0 : ℤ)) = x := by
      dsimp only [y]
      apply Prod.ext <;> simp [Prod.sub_def]
    obtain ⟨N, K, hy, hEast, _hNorth, hBounds⟩ := hNeighborBounds y
    have hx : x ≤ γ N := by
      rw [← hyEast]
      exact hEast
    have hbound (n : ℕ) : rootRelative y N n - rootRelative x N n ≤ K := by
      have hNeighbor := (hBounds n).1
      rw [hyEast] at hNeighbor
      dsimp only [rootRelative]
      linarith
    exact hNoTopFromNeighbor y x N K hy hx hbound hfiniteX
  -- The south predecessor is covered at the same N as its north neighbor.
  have hSouthTop (x : Lattice) (hfiniteX : bE x < (⊤ : EReal)) :
      bE (x - ((0 : ℤ), (1 : ℤ))) < (⊤ : EReal) := by
    let y := x - ((0 : ℤ), (1 : ℤ))
    have hyNorth : y + ((0 : ℤ), (1 : ℤ)) = x := by
      dsimp only [y]
      apply Prod.ext <;> simp [Prod.sub_def]
    obtain ⟨N, K, hy, _hEast, hNorth, hBounds⟩ := hNeighborBounds y
    have hx : x ≤ γ N := by
      rw [← hyNorth]
      exact hNorth
    have hbound (n : ℕ) : rootRelative y N n - rootRelative x N n ≤ K := by
      have hNeighbor := (hBounds n).2
      rw [hyNorth] at hNeighbor
      dsimp only [rootRelative]
      linarith
    exact hNoTopFromNeighbor y x N K hy hx hbound hfiniteX
  -- Propagate no-top from the northeast to every signed lattice site.
  have hNoTop : ∀ x : Lattice, bE x < (⊤ : EReal) :=
    all_lattice_of_northeast_and_west_south u
      (fun x => bE x < (⊤ : EReal)) hNortheastTop hWestTop hSouthTop
  -- Convert only after both endpoint exclusions hold everywhere.
  let b : Lattice → ℝ := fun x => (bE x).toReal
  have hRootReal (x : Lattice) (N : ℕ) (hN : x ≤ γ N) :
      Tendsto (rootRelative x N) atTop (𝓝 ((bE x).toReal)) := by
    have h :=
      (EReal.tendsto_toReal (ne_of_lt (hNoTop x)) (ne_of_gt (hbE x).1)).comp
        (hRootE x N hN)
    simpa only [Function.comp_def, EReal.toReal_coe] using h
  have hRootLimits : ∀ x : Lattice, ∀ N : ℕ, x ≤ γ N →
      Tendsto (fun n : ℕ =>
        lastPassage ω x
          (((γ (N + n)).1 - x.1).toNat, ((γ (N + n)).2 - x.2).toNat) -
        lastPassage ω u
          (((γ (N + n)).1 - u.1).toNat, ((γ (N + n)).2 - u.2).toNat))
        atTop (𝓝 (b x)) := by
    intro x N hN
    simpa only [rootRelative, b] using hRootReal x N hN
  exact unique_additive_pair_field_of_root_limits
    ω u γ hescape₁ hescape₂ b hRootLimits

end LPP.Busemann
