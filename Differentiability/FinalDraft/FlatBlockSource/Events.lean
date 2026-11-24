/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatBlockSource.Geometry
public import Differentiability.FinalDraft.FlatBlockSource.Cylinder
public import LPP_Foundations.Probability.EnvironmentSwap
public import LPP_Foundations.Probability.TranslationEquiv
public import Mathlib.Data.Nat.Dist
import Differentiability.Model.FiniteLevelStripCardinality
import LPP_Foundations.Probability.DisjointSupportEvents
import Mathlib.Tactic

/-! One-dependence of the entire confined crossings, as in Durrett
(1984), Section 9, property (i). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace LPPDifferentiability.FinalDraft.FlatBlockSource

/-- Figure 7's rectangular support for both parallelograms in the rotated coordinates. -/
def blockSupport (N : ℕ) (w : ℤ) (a : Lattice) : Set Lattice :=
  {z | a.1 + a.2 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ a.1 + a.2 + 22 * (N : ℤ) ∧
    |(z.1 : ℝ) - (z.2 : ℝ) - ((a.1 : ℝ) - (a.2 : ℝ))| ≤ 22 * w}

/-- The rotated rectangle has an exact finite enumeration. -/
theorem exists_finset_blockSupport (N : ℕ) (w : ℤ) (hw : 0 ≤ w) (a : Lattice) :
    ∃ S : Finset Lattice, ∀ z, z ∈ S ↔ z ∈ blockSupport N w a := by
  obtain ⟨S, hS, -⟩ := exists_finset_signed_level_tube (1 / 2) (11 * (w : ℝ))
    (fun _ => ((a.1 : ℝ) - (a.2 : ℝ)) / 2) (a.1 + a.2) (22 * N) (by positivity)
  refine ⟨S, fun z => ?_⟩
  rw [hS]
  simp only [blockSupport, mem_ofPred_eq, Nat.cast_mul, Nat.cast_ofNat, and_congr_right_iff]
  intro _ _
  rw [show (1 - (1 / 2 : ℝ)) * (z.1 : ℝ) - (1 / 2 : ℝ) * (z.2 : ℝ) -
      ((a.1 : ℝ) - (a.2 : ℝ)) / 2 =
      ((z.1 : ℝ) - (z.2 : ℝ) - ((a.1 : ℝ) - (a.2 : ℝ))) / 2 by ring, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  constructor <;> intro h <;> linarith only [h]

/-- A confined trace stays inside the block's transverse support. -/
theorem RightConfined.abs_rotation_le {N : ℕ} {w : ℤ} {x : ℕ → ℤ}
    (hx : RightConfined N w x) (hN : 0 < N) (hw : 0 ≤ w) {t : ℕ} (ht : t ≤ 22 * N) :
    |(traceRotation x t : ℝ)| ≤ 22 * w := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have ht' : (t : ℝ) ≤ 22 * (N : ℝ) := by exact_mod_cast ht
  have hdiv : (t : ℝ) / (N : ℝ) ≤ 22 :=
    (div_le_iff₀ hN').2 (by linarith only [ht'])
  have hprod := mul_le_mul_of_nonneg_left hdiv (show 0 ≤ (w : ℝ) by exact_mod_cast hw)
  have hnonneg : 0 ≤ (w : ℝ) / (N : ℝ) * (t : ℝ) := by positivity
  have hbound := hx t ht
  rw [div_mul_eq_mul_div, mul_div_assoc] at hbound
  refine abs_le.2 ⟨?_, ?_⟩
  · rw [div_mul_eq_mul_div, mul_div_assoc] at hnonneg
    linarith only [hbound.1, hnonneg, show (0 : ℝ) ≤ (w : ℝ) by exact_mod_cast hw]
  · linarith only [hbound.2, hprod, show (0 : ℝ) ≤ (w : ℝ) by exact_mod_cast hw]

/-- Convert a transverse support bound to membership of the physical site. -/
theorem traceSite_mem_blockSupport {a : Lattice} {N : ℕ} {w : ℤ} {x : ℕ → ℤ}
    {t : ℕ} (ht : t ≤ 22 * N) (hx : |(traceRotation x t : ℝ)| ≤ 22 * w) :
    traceSite a t (x t) ∈ blockSupport N w a := by
  have hcast : (t : ℤ) ≤ 22 * (N : ℤ) := by exact_mod_cast ht
  have ht0 : (0 : ℤ) ≤ t := by positivity
  unfold blockSupport
  simp only [mem_ofPred_eq, traceSite, Prod.fst_add, Prod.snd_add]
  refine ⟨by omega, by omega, ?_⟩
  push_cast
  convert hx using 2
  push_cast [traceRotation]
  ring

/-- The confinement event depends on the open sites in the precise rectangle. -/
theorem rightBlock_local {N : ℕ} {w : ℤ} (hN : 0 < N) (hw : 0 ≤ w)
    (a : Lattice) (ω ω' : Environment)
    (h : ∀ z ∈ blockSupport N w a, ω z = 1 ↔ ω' z = 1) :
    ω ∈ RightBlock N w a ↔ ω' ∈ RightBlock N w a := by
  have transfer (f g : Environment)
      (hfg : ∀ z ∈ blockSupport N w a, f z = 1 → g z = 1)
      (hf : f ∈ RightBlock N w a) : g ∈ RightBlock N w a := by
    obtain ⟨x, hx, hc⟩ := hf
    refine ⟨x, ⟨hx.1, fun i hi => hfg _ ?_ (hx.2 i hi)⟩, hc⟩
    exact traceSite_mem_blockSupport (Nat.succ_le_of_lt hi)
      (hc.abs_rotation_le hN hw (Nat.succ_le_of_lt hi))
  exact ⟨transfer _ _ (fun z hz => (h z hz).mp), transfer _ _ (fun z hz => (h z hz).mpr)⟩

/-- The same rectangle supports the two reflected crossings. -/
theorem goodBlock_local {N : ℕ} {w : ℤ} (hN : 0 < N) (hw : 0 ≤ w)
    (a : Lattice) (ω ω' : Environment)
    (h : ∀ z ∈ blockSupport N w a, ω z = 1 ↔ ω' z = 1) :
    ω ∈ GoodBlock N w a ↔ ω' ∈ GoodBlock N w a := by
  have transfer (f g : Environment)
      (hfg : ∀ z ∈ blockSupport N w a, f z = 1 → g z = 1)
      (hf : ∃ y, OpenTrace f a (22 * N) y ∧ RightConfined N w (reflectTrace y)) :
      ∃ y, OpenTrace g a (22 * N) y ∧ RightConfined N w (reflectTrace y) := by
    obtain ⟨y, hy, hc⟩ := hf
    refine ⟨y, ⟨hy.1, fun i hi => hfg _ ?_ (hy.2 i hi)⟩, hc⟩
    have hb := hc.abs_rotation_le hN hw (Nat.succ_le_of_lt hi)
    rw [traceRotation_reflect, Int.cast_neg, abs_neg] at hb
    exact traceSite_mem_blockSupport (Nat.succ_le_of_lt hi) hb
  exact and_congr (rightBlock_local hN hw a ω ω' h)
    ⟨transfer _ _ (fun z hz => (h z hz).mp), transfer _ _ (fun z hz => (h z hz).mpr)⟩

/-- The good event at any anchor is the translated event at zero. -/
theorem goodBlock_eq_translate (N : ℕ) (w : ℤ) (a : Lattice) :
    GoodBlock N w a = (environmentTranslationEquiv a) ⁻¹' GoodBlock N w 0 := by
  ext ω
  simp only [GoodBlock, mem_ofPred_eq, mem_preimage, OpenTrace,
    environmentTranslationEquiv_apply, traceSite, zero_add]

private theorem trace_swap {ω : Environment} {n : ℕ} {x : ℕ → ℤ}
    (hx : OpenTrace ω 0 n x) : OpenTrace (environmentSwap ω) 0 n (reflectTrace x) := by
  constructor
  · intro i hi
    rcases hx.1 i hi with h | h <;>
      simp only [reflectTrace, Nat.cast_add, Nat.cast_one] <;> omega
  · intro i hi
    have he (t : ℕ) : (traceSite 0 t (reflectTrace x t)).swap = traceSite 0 t (x t) := by
      apply Prod.ext <;> simp [traceSite, reflectTrace, Prod.swap]
    rw [environmentSwap_apply, he]
    exact hx.2 i hi

/-- Diagonal reflection gives equality of the two crossing probabilities. -/
theorem goodBlock_eq_inter_swap (N : ℕ) (w : ℤ) :
    GoodBlock N w 0 = RightBlock N w 0 ∩ (environmentSwap ⁻¹' RightBlock N w 0) := by
  have hinv (x : ℕ → ℤ) : reflectTrace (reflectTrace x) = x := by
    funext t
    simp only [reflectTrace]
    omega
  ext ω
  constructor
  · rintro ⟨h, y, hy, hc⟩
    exact ⟨h, ⟨reflectTrace y, trace_swap hy, hc⟩⟩
  · rintro ⟨h, y, hy, hc⟩
    refine ⟨h, reflectTrace y, ?_, ?_⟩
    · simpa only [environmentSwap_involutive, hinv] using trace_swap hy
    · simpa only [hinv] using hc

/-- Coarse sites at sup-coordinate distance greater than one have
disjoint supports. This is Durrett's one-dependence bound. -/
theorem blockSupport_disjoint {N : ℕ} {w : ℤ} (hN : 0 < N) (hw : 0 < w)
    {u v : ℕ × ℕ} (hd : 1 < Nat.dist u.1 v.1 ∨ 1 < Nat.dist u.2 v.2) :
    Disjoint (blockSupport N w (anchor N w u)) (blockSupport N w (anchor N w v)) := by
  rw [Set.disjoint_left]
  intro z hu hv
  obtain ⟨huL, huU, huR⟩ := hu
  obtain ⟨hvL, hvU, hvR⟩ := hv
  rw [anchor_level] at huL huU hvL hvU
  let i : ℤ := (u.1 : ℤ) - v.1
  let j : ℤ := (u.2 : ℤ) - v.2
  have hN' : 0 < (N : ℤ) := by exact_mod_cast hN
  have hsum : -1 ≤ i + j ∧ i + j ≤ 1 := by
    have h₁ : -22 * (N : ℤ) ≤ 20 * (N : ℤ) * (i + j) := by
      dsimp [i, j]
      nlinarith only [hvL, huU]
    have h₂ : 20 * (N : ℤ) * (i + j) ≤ 22 * (N : ℤ) := by
      dsimp [i, j]
      nlinarith only [huL, hvU]
    constructor
    · by_contra! h
      nlinarith only [h₁, hN', mul_le_mul_of_nonneg_left (show i + j ≤ -2 by omega) hN'.le]
    · by_contra! h
      nlinarith only [h₂, hN', mul_le_mul_of_nonneg_left (show 2 ≤ i + j by omega) hN'.le]
  have hr (v : ℕ × ℕ) : ((anchor N w v).1 : ℝ) - ((anchor N w v).2 : ℝ) =
      18 * (w : ℝ) * ((v.1 : ℝ) - v.2) := by exact_mod_cast anchor_rotation N w v
  rw [hr u] at huR
  rw [hr v] at hvR
  have hu' := abs_le.mp huR
  have hv' := abs_le.mp hvR
  have hd₁ : -44 * (w : ℝ) ≤ 18 * (w : ℝ) * ((i : ℝ) - (j : ℝ)) := by
    dsimp [i, j]
    push_cast
    linarith only [hu'.2, hv'.1]
  have hd₂ : 18 * (w : ℝ) * ((i : ℝ) - (j : ℝ)) ≤ 44 * (w : ℝ) := by
    dsimp [i, j]
    push_cast
    linarith only [hu'.1, hv'.2]
  have hw' : 0 < (w : ℝ) := by exact_mod_cast hw
  have hdiff : -2 ≤ i - j ∧ i - j ≤ 2 := by
    constructor
    · by_contra! h
      have h' : (i : ℝ) - j ≤ -3 := by exact_mod_cast (show i - j ≤ -3 by omega)
      nlinarith only [hd₁, hw', mul_le_mul_of_nonneg_left h' hw'.le]
    · by_contra! h
      have h' : 3 ≤ (i : ℝ) - j := by exact_mod_cast (show 3 ≤ i - j by omega)
      nlinarith only [hd₂, hw', mul_le_mul_of_nonneg_left h' hw'.le]
  unfold Nat.dist at hd
  dsimp [i, j] at hsum hdiff
  omega

/-- One-dependent good blocks are jointly independent on separated coarse sites. -/
theorem independent_goodBlock {N : ℕ} {w : ℤ} (hN : 0 < N) (hw : 0 < w)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : Finset (ℕ × ℕ))
    (hT : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → 1 < Nat.dist u.1 v.1 ∨ 1 < Nat.dist u.2 v.2) :
    iIndepSet (fun v : {u : ℕ × ℕ // u ∈ T} => GoodBlock N w (anchor N w v.val))
      (environmentLaw ν) := by
  classical
  choose S hS using fun v : ℕ × ℕ => exists_finset_blockSupport N w hw.le (anchor N w v)
  have hloc (v : ℕ × ℕ) (ω ω' : Environment)
      (h : ∀ z ∈ S v, ω z = 1 ↔ ω' z = 1) :
      ω ∈ GoodBlock N w (anchor N w v) ↔ ω' ∈ GoodBlock N w (anchor N w v) :=
    goodBlock_local hN hw.le _ ω ω' (fun z hz => h z ((hS v z).mpr hz))
  refine iIndepSet_environment_of_disjoint_supports ν _ (fun v => S v.val)
    (fun v => measurableSet_of_open_sites _ _ (hloc v.val)) ?_ ?_
  · intro v ω ω' h
    exact hloc v.val ω ω' (fun z hz => by rw [h z hz])
  · intro u v huv
    rw [Finset.disjoint_left]
    intro z hzU hzV
    have hd := blockSupport_disjoint hN hw
      (hT u.val u.property v.val v.property (fun he => huv (Subtype.ext he)))
    exact Set.disjoint_left.mp hd ((hS u.val z).mp hzU) ((hS v.val z).mp hzV)

end LPPDifferentiability.FinalDraft.FlatBlockSource
