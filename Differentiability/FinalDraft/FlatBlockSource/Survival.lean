/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatBlockSource.Events
public import Differentiability.FinalDraft.FlatTop.Percolation
import all Differentiability.FinalDraft.FlatTop.SurvivalLaw
import Differentiability.Model.Paths.OrientedCompactness
import Mathlib.Tactic

/-! Durrett (1984), Section 9, property (ii) and the passage from a
finite set of initial seeds to survival at the origin. -/

public section

open MeasureTheory Set

namespace LPPDifferentiability.FinalDraft.FlatBlockSource

private theorem translated_survival_of_prefixes {ω : Environment} {u : Lattice}
    (h : ∀ n, (openReachSet (topSites ω) {u} n).Nonempty) :
    environmentTranslationEquiv u ω ∈ orientedSiteSurvival 1 := by
  let ω' := environmentTranslationEquiv u ω
  let G : Set (ℕ × ℕ) := {v | v = 0 ∨ ω' ((v.1 : ℤ), (v.2 : ℤ)) = 1}
  have hfinite (n : ℕ) : ∃ q : Fin (n + 1) → ℕ × ℕ, q 0 = (0, 0) ∧
      (∀ i : Fin n, q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
      ∀ i, q i ∈ G := by
    obtain ⟨v, hv⟩ := h n
    have hpre : -u + v ∈ openReachSet (topSites ω') {0} n := by
      apply (mem_openReachSet_translate (topSites ω) {0} u (-u + v) n).2
      simpa only [add_neg_cancel_left, image_singleton, add_zero] using hv
    have hlev : ({0} : Set Lattice) ⊆ levelSet 0 := by simp [singleton_subset_iff, levelSet]
    obtain ⟨x, hx, hu, -⟩ := exists_openTrace_of_reach hpre hlev
    have hx0 : x 0 = 0 := by
      have hu' : traceSite 0 0 (x 0) = 0 := hu
      simpa only [traceSite, zero_add, Prod.fst_zero] using congrArg Prod.fst hu'
    let q : Fin (n + 1) → ℕ × ℕ := fun i => ((x i).toNat, ((i.val : ℤ) - x i).toNat)
    have hq (i : Fin (n + 1)) :
        ((q i).1 : ℤ) = x i ∧ ((q i).2 : ℤ) = (i.val : ℤ) - x i := by
      have hs := hx.1.displacement 0 i.val (by omega)
      rw [zero_add, hx0, sub_zero] at hs
      exact ⟨Int.toNat_of_nonneg hs.1, Int.toNat_of_nonneg (sub_nonneg.mpr hs.2)⟩
    have hq0 : q 0 = (0, 0) := by simp [q, hx0]
    refine ⟨q, hq0, ?_, ?_⟩
    · intro i
      have hstep := hx.1 i.val i.isLt
      have hqs := hq i.succ
      have hqc := hq i.castSucc
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at hqs hqc
      rcases hstep with he | he
      · right
        apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
      · left
        apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
    · intro i
      by_cases hi : i.val = 0
      · have hi' : i = 0 := Fin.ext hi
        exact Or.inl (hi'.symm ▸ hq0)
      · right
        have ht : i.val - 1 + 1 = i.val := by omega
        have hω := hx.2 (i.val - 1) (by omega)
        rw [ht] at hω
        simpa only [(hq i).1, (hq i).2, traceSite, zero_add] using hω
  obtain ⟨v, hv0, hvstep, hvopen⟩ := exists_infinite_good_oriented_path G hfinite
  exact (mem_orientedSiteSurvival_iff_natural_ray 1 ω').2
    ⟨v, hv0, hvstep, fun i hi => (hvopen i).resolve_left hi⟩

/-- A good coarse path supplies arbitrary open physical prefixes
from one seed in the initial block. Compactness gives survival there. -/
theorem survives_from_good_coarse_path {ω : Environment} {N : ℕ} {w : ℤ}
    (hN : 0 < N) (hw : 0 < w) (v : ℕ → ℕ × ℕ)
    (hv0 : v 0 = (0, 0))
    (hvstep : ∀ i, v (i + 1) = v i + (1, 0) ∨ v (i + 1) = v i + (0, 1))
    (hgood : ∀ i, ω ∈ GoodBlock N w (anchor N w (v i))) :
    ∃ u ∈ blockSupport N w 0, environmentTranslationEquiv u ω ∈ orientedSiteSurvival 1 := by
  classical
  let a (i : ℕ) := anchor N w (v i)
  have hpaths (i : ℕ) : ∃ x y : ℕ → ℤ,
      OpenTrace ω (a i) (22 * N) x ∧ RightConfined N w x ∧
      OpenTrace ω (a i) (22 * N) y ∧ RightConfined N w (reflectTrace y) := by
    obtain ⟨⟨x, hx, hxc⟩, ⟨y, hy, hyc⟩⟩ := hgood i
    exact ⟨x, y, hx, hxc, hy, hyc⟩
  choose x y hx hxc hy hyc using hpaths
  have ha0 : a 0 = 0 := by
    simp [a, anchor, hv0]
  have hlevel (i : ℕ) : (v i).1 + (v i).2 = i := by
    induction i with
    | zero => simp [hv0]
    | succ i ih =>
      rcases hvstep i with h | h <;> rw [h] <;>
        simp only [Prod.fst_add, Prod.snd_add, add_zero] <;> omega
  have hLevel (i : ℕ) : (a i).1 + (a i).2 = (20 * (N : ℤ)) * (i : ℤ) := by
    rw [anchor_level]
    exact congrArg (fun z : ℤ => 20 * (N : ℤ) * z) (by exact_mod_cast hlevel i)
  let u := traceSite (a 0) 0 (x 0 0)
  have hu : u ∈ blockSupport N w 0 := by
    rw [← ha0]
    exact traceSite_mem_blockSupport (Nat.zero_le _) ((hxc 0).abs_rotation_le hN hw.le (Nat.zero_le _))
  have htails (i : ℕ) : ∀ t, 4 * N ≤ t → t ≤ 22 * N →
        traceSite (a i) t (x i t) ∈ openReachSet (topSites ω) {u} (20 * N * i + t) ∧
        traceSite (a i) t (y i t) ∈ openReachSet (topSites ω) {u} (20 * N * i + t) := by
    induction i with
    | zero =>
      simpa only [Nat.mul_zero, zero_add] using
        reaches_first_tails hN hw.le (hx 0) (hy 0) (hxc 0) (hyc 0)
    | succ i ih =>
      have hlev : (a (i + 1)).1 + (a (i + 1)).2 =
          (a i).1 + (a i).2 + (20 * N : ℕ) := by
        rw [hLevel, hLevel]
        push_cast
        ring
      have hfst : (a (i + 1)).1 = (a i).1 + (10 * (N : ℤ) + 9 * w) ∨
          (a (i + 1)).1 = (a i).1 + (10 * (N : ℤ) - 9 * w) := by
        rcases hvstep i with he | he
        · exact Or.inl (by simpa only [a, he] using (anchor_step_fst N w (v i)).1)
        · exact Or.inr (by simpa only [a, he] using (anchor_step_fst N w (v i)).2)
      rw [Nat.mul_succ]
      exact reaches_next_tails hN hw.le (hx i) (hy i) (hxc i) (hyc i)
        (hx (i + 1)) (hy (i + 1)) (hxc (i + 1)) (hyc (i + 1)) hlev hfst ih
  refine ⟨u, hu, translated_survival_of_prefixes (fun n => ?_)⟩
  let d := 20 * N * n + 4 * N
  have hd : n ≤ d := by
    have h := Nat.mul_le_mul_right n (show 1 ≤ 20 * N by omega)
    rw [one_mul] at h
    exact h.trans (Nat.le_add_right _ _)
  have hlong : traceSite (a n) (4 * N) (x n (4 * N)) ∈ openReachSet (topSites ω) {u} d :=
    (htails n (4 * N) le_rfl (by omega)).1
  rw [← Nat.add_sub_of_le hd, ← openReachSet_add] at hlong
  obtain ⟨w', hw', -⟩ := hlong
  exact ⟨w', hw'⟩

/-- Surviving from a finite set of initial seeds with positive probability
gives positive survival probability at the origin by translation invariance. -/
theorem measure_survival_pos_of_good_coarse_path {N : ℕ} {w : ℤ} (hN : 0 < N)
    (hw : 0 < w) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : 0 < (environmentLaw ν).real {ω | ∃ v : ℕ → ℕ × ℕ, v 0 = (0, 0) ∧
      (∀ i, v (i + 1) = v i + (1, 0) ∨ v (i + 1) = v i + (0, 1)) ∧
      ∀ i, ω ∈ GoodBlock N w (anchor N w (v i))}) :
    0 < environmentLaw ν (orientedSiteSurvival 1) := by
  let E := {ω | ∃ v : ℕ → ℕ × ℕ, v 0 = (0, 0) ∧
    (∀ i, v (i + 1) = v i + (1, 0) ∨ v (i + 1) = v i + (0, 1)) ∧
    ∀ i, ω ∈ GoodBlock N w (anchor N w (v i))}
  obtain ⟨S, hS⟩ := exists_finset_blockSupport N w hw.le 0
  let F (u : S) := environmentTranslationEquiv u.val ⁻¹' orientedSiteSurvival 1
  have hsub : E ⊆ ⋃ u : S, F u := by
    rintro ω ⟨v, h0, hstep, hgood⟩
    obtain ⟨u, hu, hs⟩ := survives_from_good_coarse_path hN hw v h0 hstep hgood
    exact mem_iUnion.mpr ⟨⟨u, (hS u).mpr hu⟩, hs⟩
  by_contra! hn
  have hzero : environmentLaw ν (orientedSiteSurvival 1) = 0 := le_antisymm hn bot_le
  have hF (u : S) : environmentLaw ν (F u) = 0 := by
    change environmentLaw ν (environmentTranslationEquiv u.val ⁻¹' orientedSiteSurvival 1) = 0
    rw [(measurePreserving_environmentTranslationEquiv ν u.val).measure_preimage_equiv, hzero]
  have hE : environmentLaw ν E = 0 :=
    le_antisymm ((measure_mono hsub).trans_eq (measure_iUnion_null hF)) bot_le
  change 0 < (environmentLaw ν).real E at h
  rw [Measure.real_def, hE] at h
  simp at h

end LPPDifferentiability.FinalDraft.FlatBlockSource
