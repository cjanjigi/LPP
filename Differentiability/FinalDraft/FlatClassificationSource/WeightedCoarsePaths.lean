/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatClassificationSource.WeightedBlocks
import all Differentiability.Model.CoarseBlackBlocks
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! # The coarse path of a dense original-weight passage -/

public section

open Finset Classical
open scoped BigOperators
namespace LPPDifferentiability.FinalDraft

/-- A walk over `N` steps has a path segment of the indicated displacement. -/
private theorem exists_passageSegment {n : ℕ} {X : ℕ → Lattice} (a N : ℕ)
    (han : a + N ≤ n)
    (hstep : ∀ i, i < n → X (i + 1) = X i + (1, 0) ∨ X (i + 1) = X i + (0, 1)) :
    ∃ j : Fin (N + 1), ((j.val : ℕ) : ℤ) = (X (a + N)).1 - (X a).1 ∧
      ∃ p : Path (X a) (passageBlockDisplacement N j),
        ∀ i, p.vertex i = X (a + i.val) := by
  obtain ⟨hx, hy, hl⟩ := walk_segment hstep (Nat.le_add_right a N) han
  let j : Fin (N + 1) := ⟨((X (a + N)).1 - (X a).1).toNat, by omega⟩
  have hj : (j.val : ℤ) = (X (a + N)).1 - (X a).1 := by dsimp only [j]; omega
  have hd := passageBlockDisplacement_level N j
  refine ⟨j, hj, ⟨fun i => X (a + i.val), by simp, ?_, ?_⟩, fun _ => rfl⟩
  · rw [Fin.val_last, hd]
    apply Prod.ext
    · simp only [Prod.fst_add, passageBlockDisplacement]
      omega
    · simp only [Prod.snd_add, passageBlockDisplacement]
      have := j.isLt
      omega
  · intro i
    simpa only [Fin.val_succ, Fin.val_castSucc, Nat.add_assoc] using
      hstep (a + i.val) (by have := i.isLt; omega)

/-- The block crossed by the walk, and the first-coordinate budget of its black blocks. -/
private theorem weighted_coarse_of_walk (ω : Environment) (hω : ∀ z, ω z ≤ 1)
    (N : ℕ) (hN : 0 < N) (c₁ s δ ε : ℝ) (hc₁ : c₁ < 1) (hδ : 0 < δ)
    (k ℓ : ℕ) (hks : s * (k + ℓ) ≤ k) (hlen : 3 * N ≤ k + ℓ)
    (X : ℕ → Lattice) (hX0 : X 0 = 0) (hXn : X (k + ℓ) = ((k : ℤ), (ℓ : ℤ)))
    (hstep : ∀ i, i < k + ℓ → X (i + 1) = X i + (1, 0) ∨ X (i + 1) = X i + (0, 1))
    (hp : (1 - ε) * (k + ℓ) ≤ ∑ i ∈ range (k + ℓ), ω (X i)) :
    ∃ q : Fin ((k + ℓ) / N - 2 + 1) → ℕ × ℕ, q 0 = (0, 0) ∧
      (∀ i : Fin ((k + ℓ) / N - 2), q i.succ = q i.castSucc + (1, 0) ∨
        q i.succ = q i.castSucc + (0, 1)) ∧
      ((univ.filter fun j =>
          IsBlackPassageBlock ω N c₁ δ (((q j).1 : ℤ), ((q j).2 : ℤ))).card : ℝ) ≤
        ε * (k + ℓ) / δ + (1 - s) * (k + ℓ) / ((1 - c₁) * N) := by
  classical
  generalize hm : (k + ℓ) / N - 2 = m
  have hmN : (m + 2) * N ≤ k + ℓ := by
    have h3 : 3 ≤ (k + ℓ) / N := (Nat.le_div_iff_mul_le hN).2 hlen
    have h4 : m + 2 = (k + ℓ) / N := by omega
    rw [h4]
    exact Nat.div_mul_le_self _ _
  obtain ⟨T, A, q, hT, hT1, hTN, hTmono, hTm, hjT, hb, hAf, hq12, hq0, hqstep⟩ :=
    coarse_walk_geometry hX0 hstep N m hN hmN
  refine ⟨q, hq0, hqstep, ?_⟩
  · suffices hmain : ∀ S : Finset (Fin (m + 1)),
        (∀ j, j ∈ S → IsBlackPassageBlock ω N c₁ δ (((q j).1 : ℤ), ((q j).2 : ℤ))) →
        (S.card : ℝ) ≤ ε * (k + ℓ) / δ +
          (1 - s) * (k + ℓ) / ((1 - c₁) * N) from
      hmain _ (fun j hj => (mem_filter.1 hj).2)
    intro S hS
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hD : 0 < (1 - c₁) * N := mul_pos (by linarith) hNpos
    have hTjN : ∀ j : Fin (m + 1), T j.val + N ≤ k + ℓ := fun j => by
      have h1 := hTmono (j.val + 1) (m + 1) (by have := j.isLt; omega)
      have h2 := hT1 j.val
      omega
    have hcard := Finset.card_filter_add_card_filter_not (s := S)
      (fun j : Fin (m + 1) => c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ))
    let Good := S.filter fun j : Fin (m + 1) =>
      c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ)
    let I (j : Fin (m + 1)) := Finset.Ico (T j.val) (T j.val + N)
    let deficit (i : ℕ) := 1 - ω (X i)
    have htotal : ∑ i ∈ range (k + ℓ), deficit i ≤ ε * (k + ℓ) := by
      simp only [deficit, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one, Nat.cast_add]
      linarith
    have hGood : ∀ j ∈ Good, δ ≤ ∑ i ∈ I j, deficit i := by
      intro j hj
      obtain ⟨hjS, hjg⟩ := mem_filter.1 hj
      have hjm : j.val ≤ m := Nat.lt_succ_iff.1 j.isLt
      obtain ⟨a0, a1, a2, a3⟩ := hAf j.val hjm
      have hTj := hjT j.val hjm
      have hN1 := hTN j.val
      obtain ⟨hx1, hx2, hx3⟩ := hb (T j.val - 1) (by omega)
      obtain ⟨hu1, hu2, hu3⟩ := hb (T j.val) hTj
      obtain ⟨s1, s2, s3⟩ := walk_segment hstep (a := T j.val - 1) (b := T j.val)
        (by omega) hTj
      have hTj' : (T j.val : ℤ) = ((j.val : ℤ) + 1) * N := by rw [hT]; push_cast; ring
      have hcast : ((T j.val - 1 : ℕ) : ℤ) = (T j.val : ℤ) - 1 := by omega
      let z : Lattice := (((q j).1 : ℤ), ((q j).2 : ℤ))
      have hz1 : (N : ℤ) * z.1 ≤ (X (T j.val)).1 := by
        dsimp only [z]; rw [(hq12 j).1]; linarith
      have hz2 : (N : ℤ) * z.2 ≤ (X (T j.val)).2 := by
        dsimp only [z]; rw [(hq12 j).2]; nlinarith
      have hzLevel : ((X (T j.val)).1 - (N : ℤ) * z.1) +
          ((X (T j.val)).2 - (N : ℤ) * z.2) = N := by
        dsimp only [z]; rw [(hq12 j).1, (hq12 j).2]; nlinarith
      let i : Fin (N + 1) := ⟨((X (T j.val)).1 - (N : ℤ) * z.1).toNat, by omega⟩
      have hi : (i.val : ℤ) = (X (T j.val)).1 - (N : ℤ) * z.1 := by dsimp only [i]; omega
      have hstart : passageBlockStart N z i = X (T j.val) := by
        unfold passageBlockStart passageBlockCorner
        apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
      obtain ⟨r, hr, p, hp⟩ := exists_passageSegment (T j.val) N (hTjN j) hstep
      have hcastR : (r.val : ℝ) = (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ) := by
        exact_mod_cast hr
      have hB := hS j hjS i r (hcastR ▸ hjg)
      rw [hstart] at hB
      have hg := (pathWeight_le_lastPassage ω p).trans hB
      have hd := passageBlockDisplacement_level N r
      have hsum : pathWeight ω p = ∑ t ∈ range N, ω (X (T j.val + t)) := by
        unfold pathWeight
        simp only [hp, Fin.val_castSucc]
        rw [Fin.sum_univ_eq_sum_range (fun t => ω (X (T j.val + t))), hd]
      rw [hsum] at hg
      simp only [I, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, deficit,
        Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left,
        nsmul_eq_mul, mul_one]
      linarith
    have hdis : (↑Good : Set (Fin (m + 1))).PairwiseDisjoint I := by
      intro j hj j' hj' hne
      change Disjoint (I j) (I j')
      rw [Finset.disjoint_left]
      intro i hi hi'
      rw [Finset.mem_Ico] at hi hi'
      have hne' : j.val ≠ j'.val := fun h => hne (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne hne' with h | h
      · have := hTmono (j.val + 1) j'.val h
        have := hT1 j.val
        omega
      · have := hTmono (j'.val + 1) j.val h
        have := hT1 j'.val
        omega
    have hsub : Good.biUnion I ⊆ range (k + ℓ) := by
      intro i hi
      obtain ⟨j, _, hj⟩ := mem_biUnion.1 hi
      have hbound := hTjN j
      rw [Finset.mem_Ico] at hj
      exact mem_range.2 (by omega)
    have hGle : (Good.card : ℝ) * δ ≤ ε * (k + ℓ) := by
      have hsum := Finset.card_nsmul_le_sum _ _ _ hGood
      rw [nsmul_eq_mul, ← Finset.sum_biUnion hdis] at hsum
      exact hsum.trans ((Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => sub_nonneg.mpr (hω (X i)))).trans htotal)
    obtain ⟨Y, hY⟩ : ∃ Y : ℕ → ℤ, ∀ j, Y j = (X (T j)).2 :=
      ⟨fun j => (X (T j)).2, fun _ => rfl⟩
    have hseg : ∀ j : Fin (m + 1), 0 ≤ (X (T j.val + N)).2 - (X (T j.val)).2 ∧
        ((X (T j.val + N)).1 - (X (T j.val)).1) +
          ((X (T j.val + N)).2 - (X (T j.val)).2) = N := fun j => by
      obtain ⟨s1, s2, s3⟩ := walk_segment hstep (a := T j.val) (b := T j.val + N)
        (by omega) (hTjN j)
      constructor
      · omega
      · omega
    have hsumZ : ∑ j ∈ range (m + 1), ((X (T j + N)).2 - (X (T j)).2) ≤ (ℓ : ℤ) := by
      have e : ∀ j, (X (T j + N)).2 - (X (T j)).2 = Y (j + 1) - Y j := by
        intro j; rw [hY, hY, hT1]
      have hs : ∑ j ∈ range (m + 1), ((X (T j + N)).2 - (X (T j)).2) = Y (m + 1) - Y 0 := by
        rw [← Finset.sum_range_sub Y (m + 1)]
        exact Finset.sum_congr rfl (fun j _ => e j)
      rw [hs, hY, hY]
      obtain ⟨s1, s2, s3⟩ := walk_segment hstep (a := T (m + 1)) (b := k + ℓ) hTm le_rfl
      obtain ⟨z1, z2, z3⟩ := hb (T 0) (hjT 0 (Nat.zero_le m))
      have s2' : (X (T (m + 1))).2 ≤ (ℓ : ℤ) := by
        have h := s2
        rw [hXn] at h
        exact h
      omega
    have hsumR : ∑ j : Fin (m + 1), (((X (T j.val + N)).2 - (X (T j.val)).2 : ℤ) : ℝ) ≤ ℓ := by
      rw [Fin.sum_univ_eq_sum_range (fun j => (((X (T j + N)).2 - (X (T j)).2 : ℤ) : ℝ))
        (m + 1)]
      have h : ((∑ j ∈ range (m + 1), ((X (T j + N)).2 - (X (T j)).2) : ℤ) : ℝ) ≤ ℓ := by
        exact_mod_cast hsumZ
      rwa [Int.cast_sum] at h
    have hterm : ∀ j ∈ S.filter (fun j : Fin (m + 1) =>
          ¬ (c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ))),
        (1 - c₁) * N ≤ (((X (T j.val + N)).2 - (X (T j.val)).2 : ℤ) : ℝ) := by
      intro j hj
      have hjn := (Finset.mem_filter.1 hj).2
      have hxy : ((((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ) +
          (((X (T j.val + N)).2 - (X (T j.val)).2 : ℤ) : ℝ)) = N := by
        exact_mod_cast (hseg j).2
      push Not at hjn
      linarith
    have hBle : ((S.filter (fun j : Fin (m + 1) =>
          ¬ (c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ)))).card : ℝ) *
        ((1 - c₁) * N) ≤ ℓ := by
      have h1 := Finset.card_nsmul_le_sum _ _ _ hterm
      rw [nsmul_eq_mul] at h1
      refine h1.trans (le_trans ?_ hsumR)
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => ?_)
      exact_mod_cast (hseg j).1
    have hcardR : (S.card : ℝ) =
        ((S.filter fun j : Fin (m + 1) =>
          c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ)).card : ℝ) +
        ((S.filter (fun j : Fin (m + 1) =>
          ¬ (c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ)))).card : ℝ) := by
      exact_mod_cast hcard.symm
    have hGR : (Good.card : ℝ) ≤ ε * (k + ℓ) / δ := (le_div_iff₀ hδ).2 hGle
    have hbad : ((S.filter (fun j : Fin (m + 1) =>
          ¬ (c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ)))).card : ℝ) ≤
        (1 - s) * (k + ℓ) / ((1 - c₁) * N) := by
      rw [le_div_iff₀ hD]
      nlinarith
    dsimp only [Good] at hGR
    linarith

/-- The corrected coarse path has few original-passage black blocks when the original path
collects almost the largest possible weight. -/
theorem coarse_path_few_black_passage_blocks (ω : Environment) (hω : ∀ z, ω z ≤ 1)
    (N : ℕ) (hN : 0 < N) (c₁ s δ ε : ℝ) (hc₁ : c₁ < 1) (hδ : 0 < δ)
    (k ℓ : ℕ) (hks : s * (k + ℓ) ≤ k) (hlen : 3 * N ≤ k + ℓ)
    (hG : (1 - ε) * (k + ℓ) ≤ lastPassage ω 0 (k, ℓ)) :
    ∃ q : Fin ((k + ℓ) / N - 2 + 1) → ℕ × ℕ, q 0 = (0, 0) ∧
      (∀ i : Fin ((k + ℓ) / N - 2), q i.succ = q i.castSucc + (1, 0) ∨
        q i.succ = q i.castSucc + (0, 1)) ∧
      ((univ.filter fun j =>
          IsBlackPassageBlock ω N c₁ δ (((q j).1 : ℤ), ((q j).2 : ℤ))).card : ℝ) ≤
        ε * (k + ℓ) / δ + (1 - s) * (k + ℓ) / ((1 - c₁) * N) := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω 0 (k, ℓ)
  obtain ⟨X, h0, hn, hstep, hvertex⟩ := exists_walk p
  have hV (i : Fin (k + ℓ)) : p.vertex i.castSucc = X i.val := by
    by_cases hi : i.val = 0
    · rw [hi, h0]
      exact (congrArg p.vertex (Fin.ext hi)).trans p.start
    · let j : Fin (k + ℓ) := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hj : j.succ = i.castSucc := Fin.ext (by
        simp only [Fin.val_succ, Fin.val_castSucc, j]
        omega)
      rw [← hj, hvertex j]
      congr 1
      dsimp only [j]
      omega
  have hs : pathWeight ω p = ∑ i ∈ range (k + ℓ), ω (X i) := by
    unfold pathWeight
    simp_rw [hV]
    exact Fin.sum_univ_eq_sum_range (fun i => ω (X i)) (k + ℓ)
  rw [← hp, hs] at hG
  exact weighted_coarse_of_walk ω hω N hN c₁ s δ ε hc₁ hδ k ℓ hks hlen X h0 hn hstep hG

end LPPDifferentiability.FinalDraft
