/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Model.LastPassage.OptimalSplit
public import LPP_Foundations.Model.LastPassage.GeodesicSegments
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Order.MonotoneConvergence
import Busemann.Geometry.GeodesicPassageDifferenceLimit
import Mathlib.Tactic

/-! Signed-site passage-difference limits along an escaping geodesic. -/

@[expose] public section
open LPPDifferentiability Filter
open scoped Topology

namespace LPP.Busemann

private def displacement (a b : Lattice) : ℕ × ℕ :=
  ((b.1 - a.1).toNat, (b.2 - a.2).toNat)

private theorem displacement_cast (a b : Lattice) (h : a ≤ b) :
    a + (((displacement a b).1 : ℤ), ((displacement a b).2 : ℤ)) = b := by
  have h1 := Int.toNat_of_nonneg (show 0 ≤ b.1 - a.1 by have := h.1; omega)
  have h2 := Int.toNat_of_nonneg (show 0 ≤ b.2 - a.2 by have := h.2; omega)
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, displacement] <;> omega

private theorem displacement_add (a b c : Lattice) (hab : a ≤ b) (hbc : b ≤ c) :
    displacement a b + displacement b c = displacement a c := by
  have h1 := congrArg Prod.fst (displacement_cast a b hab)
  have h2 := congrArg Prod.snd (displacement_cast a b hab)
  have h3 := congrArg Prod.fst (displacement_cast b c hbc)
  have h4 := congrArg Prod.snd (displacement_cast b c hbc)
  have h5 := congrArg Prod.fst (displacement_cast a c (le_trans hab hbc))
  have h6 := congrArg Prod.snd (displacement_cast a c (le_trans hab hbc))
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2 h3 h4 h5 h6
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;>
    apply Int.ofNat_inj.mp <;> push_cast <;> omega

private theorem displacement_unique (a b : Lattice) (d : ℕ × ℕ)
    (h : a + ((d.1 : ℤ), (d.2 : ℤ)) = b) (hab : a ≤ b) :
    d = displacement a b := by
  have h' := displacement_cast a b hab
  have h1 := congrArg Prod.fst (h.trans h'.symm)
  have h2 := congrArg Prod.snd (h.trans h'.symm)
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  apply Prod.ext <;> omega

private theorem passage_through (ω : Environment) (a b c : Lattice)
    (hab : a ≤ b) (hbc : b ≤ c) :
    lastPassage ω a (displacement a b) + lastPassage ω b (displacement b c) ≤
      lastPassage ω a (displacement a c) := by
  have h := lastPassage_superadditive ω a (displacement a b) (displacement b c)
  rw [displacement_cast a b hab, displacement_add a b c hab hbc] at h
  exact h

/-- Along one coordinate-escaping geodesic, every signed site has a unique
passage-difference limit strictly above minus infinity, possibly plus infinity.
Every valid entry time gives the same limit and its finite initial lower bound.
Strong Existence, equations g408b and g452, lines 1615–1642. -/
theorem exists_unique_geodesic_passage_difference_ereal_limit
    (ω : LPPDifferentiability.Environment)
    (u : LPPDifferentiability.Lattice)
    (γ : ℕ → LPPDifferentiability.Lattice)
    (hstart : γ 0 = u)
    (hsteps : ∀ n : ℕ,
      γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
        γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ)))
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
  have hmonoγ : Monotone γ := by
    apply monotone_nat_of_le_succ
    intro n
    rcases hsteps n with he | hn
    · rw [he]
      constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
    · rw [hn]
      constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
  have huγ (n : ℕ) : u ≤ γ n := by
    simpa only [hstart] using hmonoγ (Nat.zero_le n)
  have hden (t : ℕ) :
      lastPassage ω u (displacement u (γ (t + 1))) =
        lastPassage ω u (displacement u (γ t)) +
          lastPassage ω (γ t) (displacement (γ t) (γ (t + 1))) := by
    have hseg := hsegments 0 (t + 1) (by omega)
    rw [hstart] at hseg
    obtain ⟨d, p, hdlen, htrace, hp⟩ := hseg
    have htrace' (i : Fin (d.1 + d.2 + 1)) : p.vertex i = γ i.val := by
      simpa only [Nat.zero_add] using htrace i
    have hend : u + ((d.1 : ℤ), (d.2 : ℤ)) = γ (t + 1) := by
      rw [← p.finish, htrace']
      simp only [Fin.val_last, hdlen]
    have hd : d = displacement u (γ (t + 1)) :=
      displacement_unique u (γ (t + 1)) d hend (huγ (t + 1))
    let i : Fin (d.1 + d.2 + 1) := ⟨t, by omega⟩
    have hi : p.vertex i = γ t := htrace' i
    have ha : p.splitDisplacement i = displacement u (γ t) := by
      apply displacement_unique u (γ t) (p.splitDisplacement i)
      exact (p.split_vertex i).symm.trans hi
      exact huγ t
    have hadd := displacement_add u (γ t) (γ (t + 1)) (huγ t)
      (hmonoγ (Nat.le_succ t))
    have hb : d - displacement u (γ t) = displacement (γ t) (γ (t + 1)) := by
      rw [hd, ← hadd]
      apply Prod.ext <;> simp
    have hs := p.lastPassage_eq_split_of_maximizing ω hp i
    rw [ha, displacement_cast u (γ t) (huγ t), hb, hd] at hs
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
    lastPassage ω x (displacement x (γ (N + n))) -
      lastPassage ω u (displacement u (γ (N + n)))
  have hprops (N : ℕ) (hN : x ≤ γ N) : Monotone (f N) := by
    have hvalid (n : ℕ) : x ≤ γ (N + n) :=
      le_trans hN (hmonoγ (Nat.le_add_right N n))
    apply monotone_nat_of_le_succ
    intro n
    have hgrow := passage_through ω x (γ (N + n)) (γ (N + n + 1))
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
