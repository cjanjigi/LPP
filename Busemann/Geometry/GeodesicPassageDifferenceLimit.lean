/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Model.LastPassage.OptimalSplit
public import LPP_Foundations.Model.LastPassage.GeodesicSegments
public import LPP_Foundations.Model.Paths.UpRightRay
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Instances.Real.Lemmas
import LPP_Foundations.Model.LastPassage.PassageDifferenceLimits
import Mathlib.Tactic

/-! Monotone passage differences along an escaping geodesic. -/

@[expose] public section
open LPPDifferentiability Filter
open scoped Topology

namespace LPP.Busemann

/-- Along an escaping geodesic, passage differences based at its signed start
have one finite monotone limit at each site in the starting northeast quadrant.
Every admissible entry time gives the same limit and the source bounds. -/
theorem exists_unique_quadrant_geodesic_passage_difference_limit
    (ω : LPPDifferentiability.Environment)
    (u : LPPDifferentiability.Lattice)
    (γ : ℕ → LPPDifferentiability.Lattice)
    (hstart : γ 0 = u)
    (hsteps : IsUpRightRay γ)
    (hsegments : LPPDifferentiability.has_maximizing_segments ω γ)
    (hescape₁ : Tendsto (fun n : ℕ => (γ n).1) atTop atTop)
    (hescape₂ : Tendsto (fun n : ℕ => (γ n).2) atTop atTop) :
    ∀ x : LPPDifferentiability.Lattice, u ≤ x →
      ∃! b : ℝ, ∀ N : ℕ, x ≤ γ N →
        let f : ℕ → ℝ := fun n =>
          LPPDifferentiability.lastPassage ω x
            (((γ (N + n)).1 - x.1).toNat,
              ((γ (N + n)).2 - x.2).toNat) -
            LPPDifferentiability.lastPassage ω u
              (((γ (N + n)).1 - u.1).toNat,
                ((γ (N + n)).2 - u.2).toNat)
        Monotone f ∧ Tendsto f atTop (𝓝 b) ∧
          f 0 ≤ b ∧
          b ≤ -LPPDifferentiability.lastPassage ω u
            ((x.1 - u.1).toNat, (x.2 - u.2).toNat)
 := by
  classical
  have hmonoγ : Monotone γ := hsteps.monotone
  have huγ (n : ℕ) : u ≤ γ n := by
    simpa only [hstart] using hmonoγ (Nat.zero_le n)
  -- Every step is an exact passage decomposition of the actual geodesic.
  have hden (t : ℕ) :
      lastPassage ω u (natDisplacement u (γ (t + 1))) =
        lastPassage ω u (natDisplacement u (γ t)) +
          lastPassage ω (γ t) (natDisplacement (γ t) (γ (t + 1))) := by
    have hseg := hsegments 0 (t + 1) (by omega)
    rw [hstart] at hseg
    obtain ⟨d, p, hdlen, htrace, hp⟩ := hseg
    have htrace' (i : Fin (d.1 + d.2 + 1)) : p.vertex i = γ i.val := by
      simpa only [Nat.zero_add] using htrace i
    have hend : u + ((d.1 : ℤ), (d.2 : ℤ)) = γ (t + 1) := by
      rw [← p.finish, htrace']
      simp only [Fin.val_last, hdlen]
    have hd : d = natDisplacement u (γ (t + 1)) :=
      natDisplacement_unique u (γ (t + 1)) d hend (huγ (t + 1))
    let i : Fin (d.1 + d.2 + 1) := ⟨t, by omega⟩
    have hi : p.vertex i = γ t := htrace' i
    have ha : p.splitDisplacement i = natDisplacement u (γ t) := by
      apply natDisplacement_unique u (γ t) (p.splitDisplacement i)
      exact (p.split_vertex i).symm.trans hi
      exact huγ t
    have hadd := natDisplacement_add u (γ t) (γ (t + 1)) (huγ t)
      (hmonoγ (Nat.le_succ t))
    have hb : d - natDisplacement u (γ t) = natDisplacement (γ t) (γ (t + 1)) := by
      rw [hd, ← hadd]
      apply Prod.ext <;> simp
    have hs := p.lastPassage_eq_split_of_maximizing ω hp i
    rw [ha, add_cast_natDisplacement u (γ t) (huγ t), hb, hd] at hs
    exact hs
  intro x hux
  have hentry : ∃ N : ℕ, x ≤ γ N := by
    obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1 ((Filter.tendsto_atTop.1 hescape₁) x.1)
    obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.1 ((Filter.tendsto_atTop.1 hescape₂) x.2)
    refine ⟨max n₁ n₂, ?_, ?_⟩
    · exact hn₁ _ (le_max_left _ _)
    · exact hn₂ _ (le_max_right _ _)
  let f (N n : ℕ) : ℝ :=
    lastPassage ω x (natDisplacement x (γ (N + n))) -
      lastPassage ω u (natDisplacement u (γ (N + n)))
  have hprops (N : ℕ) (hN : x ≤ γ N) :
      Monotone (f N) ∧
        ∀ n, f N n ≤ -lastPassage ω u (natDisplacement u x) := by
    have hvalid (n : ℕ) : x ≤ γ (N + n) :=
      le_trans hN (hmonoγ (Nat.le_add_right N n))
    constructor
    · apply monotone_nat_of_le_succ
      intro n
      have hgrow := lastPassage_superadditive_between ω x (γ (N + n)) (γ (N + n + 1))
        (hvalid n) (hmonoγ (Nat.le_succ (N + n)))
      have heq := hden (N + n)
      dsimp only [f]
      rw [show N + (n + 1) = N + n + 1 by omega, heq]
      linarith
    · intro n
      have hbound := lastPassage_superadditive_between ω u x (γ (N + n)) hux (hvalid n)
      dsimp only [f]
      linarith
  obtain ⟨N₀, hN₀⟩ := hentry
  have hm := (hprops N₀ hN₀).1
  have hbdd : BddAbove (Set.range (f N₀)) :=
    ⟨-lastPassage ω u (natDisplacement u x), by rintro _ ⟨n, rfl⟩; exact (hprops N₀ hN₀).2 n⟩
  let b := ⨆ n, f N₀ n
  have hlim : Tendsto (f N₀) atTop (𝓝 b) := tendsto_atTop_ciSup hm hbdd
  have hall (N : ℕ) : Tendsto (f N) atTop (𝓝 b) := by
    have hshift : Tendsto (fun n => f N₀ (n + (max N N₀ - N₀))) atTop (𝓝 b) :=
      hlim.comp (tendsto_add_atTop_nat _)
    have heq : (fun n => f N₀ (n + (max N N₀ - N₀))) =
        (fun n => f N (n + (max N N₀ - N))) := by
      funext n
      have hindex : N₀ + (n + (max N N₀ - N₀)) =
          N + (n + (max N N₀ - N)) := by omega
      simp only [f, hindex]
    rw [heq] at hshift
    exact (tendsto_add_atTop_iff_nat _).1 hshift
  refine ⟨b, ?_, ?_⟩
  · intro N hN
    have hNlim := hall N
    have hNmono := (hprops N hN).1
    change Monotone (f N) ∧ Tendsto (f N) atTop (𝓝 b) ∧
      f N 0 ≤ b ∧ b ≤ -lastPassage ω u (natDisplacement u x)
    exact ⟨hNmono, hNlim, hNmono.ge_of_tendsto hNlim 0,
      le_of_tendsto' hNlim ((hprops N hN).2)⟩
  · intro b' hb'
    have hh := hb' N₀ hN₀
    exact tendsto_nhds_unique hh.2.1 hlim

end LPP.Busemann
