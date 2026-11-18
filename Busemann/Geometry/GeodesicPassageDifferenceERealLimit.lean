/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Model.LastPassage.OptimalSplit
public import LPP_Foundations.Model.LastPassage.GeodesicSegments
public import LPP_Foundations.Model.Paths.UpRightRay
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Order.MonotoneConvergence
import LPP_Foundations.Model.LastPassage.PassageDifferenceLimits
import Busemann.Geometry.GeodesicPassageDifferenceLimit
import Mathlib.Tactic

/-! Signed-site passage-difference limits along an escaping geodesic. -/

@[expose] public section
open LPPDifferentiability Filter
open scoped Topology

namespace LPP.Busemann

/-- Along one coordinate-escaping geodesic, every signed site has a unique
passage-difference limit strictly above minus infinity, possibly plus infinity.
Every valid entry time gives the same limit and its finite initial lower bound.
Strong Existence, equations g408b and g452, lines 1615–1642. -/
theorem exists_unique_geodesic_passage_difference_ereal_limit
    (ω : LPPDifferentiability.Environment)
    (u : LPPDifferentiability.Lattice)
    (γ : ℕ → LPPDifferentiability.Lattice)
    (hstart : γ 0 = u)
    (hsteps : IsUpRightRay γ)
    (hsegments : LPPDifferentiability.has_maximizing_segments ω γ)
    (hescape₁ : Tendsto (fun n : ℕ => (γ n).1) atTop atTop)
    (hescape₂ : Tendsto (fun n : ℕ => (γ n).2) atTop atTop) :
    ∀ x : LPPDifferentiability.Lattice,
      ∃! b : EReal, (⊥ : EReal) < b ∧
        ∀ N : ℕ, x ≤ γ N →
          let f : ℕ → ℝ := fun n =>
            LPPDifferentiability.lastPassage ω x
              (((γ (N + n)).1 - x.1).toNat,
                ((γ (N + n)).2 - x.2).toNat) -
              LPPDifferentiability.lastPassage ω u
                (((γ (N + n)).1 - u.1).toNat,
                  ((γ (N + n)).2 - u.2).toNat)
          Monotone f ∧
            Tendsto (fun n : ℕ => (f n : EReal)) atTop (𝓝 b) ∧
            (f 0 : EReal) ≤ b := by
  classical
  have hmonoγ : Monotone γ := hsteps.monotone
  have huγ (n : ℕ) : u ≤ γ n := by
    simpa only [hstart] using hmonoγ (Nat.zero_le n)
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
  intro x
  have hentry : ∃ N : ℕ, x ≤ γ N := by
    obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1
      ((Filter.tendsto_atTop.1 hescape₁) x.1)
    obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.1
      ((Filter.tendsto_atTop.1 hescape₂) x.2)
    refine ⟨max n₁ n₂, ?_⟩
    constructor
    · exact hn₁ _ (le_max_left _ _)
    · exact hn₂ _ (le_max_right _ _)
  let f (N n : ℕ) : ℝ :=
    lastPassage ω x (natDisplacement x (γ (N + n))) -
      lastPassage ω u (natDisplacement u (γ (N + n)))
  have hprops (N : ℕ) (hN : x ≤ γ N) : Monotone (f N) := by
    have hvalid (n : ℕ) : x ≤ γ (N + n) :=
      le_trans hN (hmonoγ (Nat.le_add_right N n))
    apply monotone_nat_of_le_succ
    intro n
    have hgrow := lastPassage_superadditive_between ω x (γ (N + n)) (γ (N + n + 1))
      (hvalid n) (hmonoγ (Nat.le_succ (N + n)))
    have heq := hden (N + n)
    dsimp only [f]
    rw [show N + (n + 1) = N + n + 1 by omega, heq]
    linarith
  obtain ⟨N₀, hN₀⟩ := hentry
  have hm : Monotone (fun n : ℕ => (f N₀ n : EReal)) := by
    intro a b hab
    exact EReal.coe_le_coe_iff.mpr (hprops N₀ hN₀ hab)
  let b : EReal := ⨆ n : ℕ, (f N₀ n : EReal)
  have hlim : Tendsto (fun n : ℕ => (f N₀ n : EReal)) atTop (𝓝 b) := by
    dsimp only [b]
    exact tendsto_atTop_iSup hm
  have hpos : (⊥ : EReal) < b := by
    have hfinite : (⊥ : EReal) < (f N₀ 0 : EReal) := EReal.bot_lt_coe _
    have hle : (f N₀ 0 : EReal) ≤ b := le_iSup (fun n : ℕ => (f N₀ n : EReal)) 0
    exact lt_of_lt_of_le hfinite hle
  have hall (N : ℕ) : Tendsto (fun n : ℕ => (f N n : EReal)) atTop (𝓝 b) := by
    let s₀ := max N N₀ - N₀
    let sN := max N N₀ - N
    have hshift : Tendsto (fun n : ℕ => (f N₀ (n + s₀) : EReal)) atTop (𝓝 b) :=
      hlim.comp (tendsto_add_atTop_nat s₀)
    have heq : (fun n : ℕ => (f N₀ (n + s₀) : EReal)) =
        (fun n : ℕ => (f N (n + sN) : EReal)) := by
      funext n
      have hindex : N₀ + (n + s₀) = N + (n + sN) := by
        dsimp [s₀, sN]
        omega
      simp only [f, hindex]
    rw [heq] at hshift
    exact (tendsto_add_atTop_iff_nat sN).1 hshift
  refine ⟨b, ⟨hpos, ?_⟩, ?_⟩
  · intro N hN
    have hNmono : Monotone (f N) := hprops N hN
    have hNlim := hall N
    have hNmonoE : Monotone (fun n : ℕ => (f N n : EReal)) := by
      intro a c hac
      exact EReal.coe_le_coe_iff.mpr (hNmono hac)
    have hNinitial : (f N 0 : EReal) ≤ b := hNmonoE.ge_of_tendsto hNlim 0
    change Monotone (f N) ∧
      Tendsto (fun n : ℕ => (f N n : EReal)) atTop (𝓝 b) ∧
      (f N 0 : EReal) ≤ b
    exact ⟨hNmono, hNlim, hNinitial⟩
  · intro b' hb'
    have hh := hb'.2 N₀ hN₀
    exact tendsto_nhds_unique hh.2.1 hlim

end LPP.Busemann
