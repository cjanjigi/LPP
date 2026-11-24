/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatBlockSource.EdgeEstimates
public import Differentiability.FinalDraft.FlatBlockSource.Geometry
public import LPP_Foundations.Probability.TranslationEquiv
import Mathlib.Tactic

/-! The upper and lower side estimates for the entire right parallelogram,
following Durrett (1984), p. 1025. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace LPPDifferentiability.FinalDraft.FlatBlockSource

/-- The antidiagonal half-line starting at a given vertex. -/
def shiftedHalfLine (a : Lattice) : Set Lattice :=
  (fun z => a + z) '' antidiagHalfLine

/-- A vertex on the boundary level lies in the shifted half-line exactly when
its first coordinate is at most the boundary coordinate. -/
theorem traceSite_mem_shiftedHalfLine {s : ℕ} {x b : ℤ} (h : x ≤ b) :
    traceSite 0 s x ∈ shiftedHalfLine (traceSite 0 s b) := by
  refine ⟨(x - b, b - x), ⟨by omega, by omega⟩, ?_⟩
  apply Prod.ext <;> simp only [traceSite, zero_add, Prod.fst_add, Prod.snd_add] <;> omega

private theorem halfLine_reach_bdd (ω : Environment) (n : ℕ) :
    BddAbove (Prod.fst '' openReachSet (topSites ω) antidiagHalfLine n) := by
  refine ⟨n, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  simpa using bddAbove_fst_openReachSet (topSites ω) antidiagHalfLine n 0
    (fun u hu => (show u.1 + u.2 = 0 ∧ u.1 ≤ 0 from hu).2) z hz

/-- A physical trace starting left of the boundary at time `s` is
bounded at time `s+n` by the edge of that translated half-line. -/
theorem traceRotation_le_shifted_edge {ω : Environment} {x : ℕ → ℤ} {T s n : ℕ}
    (hx : OpenTrace ω 0 T x) (hst : s + n ≤ T) (b : ℤ) (hb : x s ≤ b) :
    (traceRotation x (s + n) : ℝ) ≤ 2 * (b : ℝ) - (s : ℝ) +
      rotatedEdge (environmentTranslationEquiv (traceSite 0 s b) ω) n := by
  let a := traceSite 0 s b
  let v := traceSite 0 (s + n) (x (s + n))
  let ω' := environmentTranslationEquiv a ω
  have hin : ({traceSite 0 s (x s)} : Set Lattice) ⊆ shiftedHalfLine a :=
    singleton_subset_iff.mpr (traceSite_mem_shiftedHalfLine hb)
  have hr : v ∈ openReachSet (topSites ω) (shiftedHalfLine a) n :=
    openReachSet_mono (Set.Subset.refl (topSites ω)) hin n (hx.segment s n hst)
  have hshift : a + (-a + v) = v := add_neg_cancel_left a v
  have hnew : -a + v ∈ openReachSet (topSites ω') antidiagHalfLine n := by
    apply (mem_openReachSet_translate (topSites ω) antidiagHalfLine a (-a + v) n).2
    simpa only [hshift, shiftedHalfLine] using hr
  have he := le_maxFirst _ (halfLine_reach_bdd ω' n) hnew
  change (-a + v).1 ≤ halfLineEdge ω' n at he
  have he' : ((x (s + n) - b : ℤ) : ℝ) ≤ (halfLineEdge ω' n : ℝ) := by
    exact_mod_cast (show x (s + n) - b ≤ halfLineEdge ω' n by
      simpa only [a, v, traceSite, Prod.fst_add, Prod.fst_neg, zero_add, sub_eq_add_neg,
        add_comm] using he)
  push_cast at he'
  change _ ≤ 2 * (b : ℝ) - (s : ℝ) + rotatedEdge ω' n
  unfold traceRotation rotatedEdge
  push_cast
  linarith only [he']

/-- The first-coordinate endpoint of the half-line just below the lower side
of the parallelogram at level `s`. The floor enforces lattice parity. -/
noncomputable def lowerBoundary (N : ℕ) (w : ℤ) (s : ℕ) : ℤ :=
  ⌊((w : ℝ) / (N : ℝ) * (s : ℝ) - 3 * w + s) / 2⌋

/-- The event of a path ending to the right of `20w` that visits the
left of the lower side at some level of the block. -/
def LeftExcursion (N : ℕ) (w : ℤ) : Set Environment :=
  {ω | ∃ x, OpenTrace ω 0 (22 * N) x ∧
    20 * (w : ℝ) < (traceRotation x (22 * N) : ℝ) ∧
    ∃ s ≤ 22 * N, (traceRotation x s : ℝ) <
      (w : ℝ) / (N : ℝ) * (s : ℝ) - 3 * w}

/-- A lower-side excursion in Durrett's proof forces one of the translated
overspeed events in (7.2). A duration below the cutoff cannot make the required
spatial displacement. -/
theorem leftExcursion_subset_deviation {α : ℝ} {N M : ℕ}
    (hN : 0 < N) (hw100 : (100 : ℤ) ≤ roundedWidth α N)
    (hMW : (M : ℤ) ≤ roundedWidth α N) :
    LeftExcursion N (roundedWidth α N) ⊆
      ⋃ n ∈ Finset.Icc M (22 * N),
        (environmentTranslationEquiv (traceSite 0 (22 * N - n)
          (lowerBoundary N (roundedWidth α N) (22 * N - n)))) ⁻¹'
          {ω | (α + α / 44) * (n : ℝ) ≤ rotatedEdge ω n} := by
  intro ω hω
  obtain ⟨x, hx, hxEnd, s, hs, hside⟩ := hω
  let w := roundedWidth α N
  let n := 22 * N - s
  let b := lowerBoundary N w s
  let a := traceSite 0 s b
  have hsn : s + n = 22 * N := Nat.add_sub_of_le hs
  have hn : n ≤ 22 * N := Nat.sub_le ..
  have hw : (100 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw100
  have hwM : (M : ℝ) ≤ (w : ℝ) := by exact_mod_cast hMW
  have hw0 : 0 ≤ (w : ℝ) := by linarith only [hw]
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hfloor : α * (N : ℝ) < (w : ℝ) + 1 := Int.lt_floor_add_one _
  have hside' : (traceRotation x s : ℝ) < (w : ℝ) / (N : ℝ) * (s : ℝ) - 3 * w := hside
  have hEnd : 20 * (w : ℝ) < (traceRotation x (22 * N) : ℝ) := hxEnd
  have htime : (s : ℝ) + (n : ℝ) = 22 * (N : ℝ) := by exact_mod_cast hsn
  have hfull : (w : ℝ) / (N : ℝ) * (22 * (N : ℝ)) = 22 * w := by
    field_simp [hNpos.ne']
  have hdiff : (w : ℝ) / (N : ℝ) * (n : ℝ) + w <
      (traceRotation x (22 * N) : ℝ) - (traceRotation x s : ℝ) := by
    have hs' : (s : ℝ) = 22 * (N : ℝ) - (n : ℝ) := by linarith only [htime]
    rw [hs', mul_sub, hfull] at hside'
    linarith only [hside', hEnd]
  have hdN : (traceRotation x (22 * N) : ℝ) - (traceRotation x s : ℝ) ≤ (n : ℝ) := by
    have hu := (hx.1.displacement s n (by omega)).2
    rw [hsn] at hu
    have hu' : (x (22 * N) : ℝ) - (x s : ℝ) ≤ (n : ℝ) := by exact_mod_cast hu
    unfold traceRotation
    push_cast
    linarith only [hu', htime]
  have hMn : M ≤ n := by
    have hspeed : 0 ≤ (w : ℝ) / (N : ℝ) * (n : ℝ) := mul_nonneg (div_nonneg hw0 hNpos.le) (Nat.cast_nonneg _)
    have hMn' : (M : ℝ) ≤ (n : ℝ) := by linarith only [hwM, hspeed, hdiff, hdN]
    exact_mod_cast hMn'
  have hb : x s ≤ b := by
    apply Int.le_floor.mpr
    unfold traceRotation at hside'
    push_cast at hside'
    linarith only [hside']
  have hb' : 2 * (b : ℝ) - (s : ℝ) ≤ (w : ℝ) / (N : ℝ) * (s : ℝ) - 3 * w := by
    have hf : (b : ℝ) ≤ ((w : ℝ) / (N : ℝ) * (s : ℝ) - 3 * w + s) / 2 := Int.floor_le _
    linarith only [hf]
  have hreach := traceRotation_le_shifted_edge hx (show s + n ≤ 22 * N by omega) b hb
  rw [hsn] at hreach
  change (traceRotation x (22 * N) : ℝ) ≤ 2 * (b : ℝ) - (s : ℝ) +
    rotatedEdge (environmentTranslationEquiv a ω) n at hreach
  have hdev : (w : ℝ) / (N : ℝ) * (n : ℝ) + w <
      rotatedEdge (environmentTranslationEquiv a ω) n := by
    have hs' : (s : ℝ) = 22 * (N : ℝ) - (n : ℝ) := by linarith only [htime]
    rw [hs', mul_sub, hfull] at hb'
    linarith only [hb', hreach, hEnd, hs']
  have hSlope : α + α / 44 ≤ ((w : ℝ) / (N : ℝ)) * (23 / 22) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hNpos]
    nlinarith only [hfloor, hw]
  have hn' : (n : ℝ) ≤ 22 * (N : ℝ) := by exact_mod_cast hn
  have hdiv : (n : ℝ) / (N : ℝ) ≤ 22 := (div_le_iff₀ hNpos).2 (by linarith only [hn'])
  have hwdiv := mul_le_mul_of_nonneg_left hdiv (hw0)
  have hpart : (w : ℝ) / (N : ℝ) * (n : ℝ) / 22 ≤ w := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    linarith only [hwdiv]
  have hoverspeed : (α + α / 44) * (n : ℝ) ≤ rotatedEdge (environmentTranslationEquiv a ω) n := by
    have hmul := mul_le_mul_of_nonneg_right hSlope (by positivity : 0 ≤ (n : ℝ))
    linarith only [hmul, hpart, hdev]
  have heq : 22 * N - n = s := by omega
  exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hMn, hn⟩,
    by simpa only [heq, mem_preimage, mem_ofPred_eq] using hoverspeed⟩⟩

/-- The translated half-line used to select the right-going crossing.
Its rotated endpoint is the rounded value of `-1.6w`. -/
noncomputable def initialBoundary (w : ℤ) : ℤ := -⌊(4 : ℝ) * (w : ℝ) / 5⌋

/-- With the uniform upper-edge estimate and no lower-side excursion,
the path reaching the actual terminal edge stays in the full parallelogram. -/
theorem rightBlock_of_edges {ω : Environment} {α : ℝ} {N : ℕ}
    (hN : 0 < N) (hw100 : (100 : ℤ) ≤ roundedWidth α N)
    (hcap : ∀ n ≤ 22 * N,
      |rotatedEdge (environmentTranslationEquiv (traceSite 0 0
          (initialBoundary (roundedWidth α N))) ω) n - α * (n : ℝ)| ≤
        (roundedWidth α N : ℝ) / 5)
    (hLeft : ω ∉ LeftExcursion N (roundedWidth α N)) :
    ω ∈ RightBlock N (roundedWidth α N) 0 := by
  let w := roundedWidth α N
  let b := initialBoundary w
  let a := traceSite 0 0 b
  let ω' := environmentTranslationEquiv a ω
  have hw : (100 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw100
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hbLo : -(8 / 5 : ℝ) * w ≤ 2 * (b : ℝ) := by
    have hf := Int.floor_le ((4 : ℝ) * (w : ℝ) / 5)
    dsimp [b, initialBoundary]
    push_cast
    linarith only [hf]
  have hbHi : 2 * (b : ℝ) ≤ -(8 / 5 : ℝ) * w + 2 := by
    have hf := Int.lt_floor_add_one ((4 : ℝ) * (w : ℝ) / 5)
    dsimp [b, initialBoundary]
    push_cast
    linarith only [hf]
  have hfLo : (w : ℝ) ≤ α * (N : ℝ) := Int.floor_le _
  have hfHi : α * (N : ℝ) < (w : ℝ) + 1 := Int.lt_floor_add_one _
  have hAt (n : ℕ) (hn : n ≤ 22 * N) :
      |rotatedEdge ω' n - α * (n : ℝ)| ≤ (w : ℝ) / 5 := hcap n hn
  have hfin := (abs_le.mp (hAt (22 * N) le_rfl)).1
  have hterminal : 20 * (w : ℝ) < 2 * (b : ℝ) + rotatedEdge ω' (22 * N) := by
    push_cast at hfin
    nlinarith only [hfLo, hfin, hbLo, hw]
  have hnonempty : (openReachSet (topSites ω') antidiagHalfLine (22 * N)).Nonempty := by
    by_contra! h
    have hzero : halfLineEdge ω' (22 * N) = 0 := by
      unfold halfLineEdge openEdge maxFirst
      rw [h, image_empty, Int.csSup_empty]
    unfold rotatedEdge at hterminal
    rw [hzero] at hterminal
    push_cast at hterminal
    linarith only [hw, hbHi, hterminal, hN']
  obtain ⟨v, hv, hve⟩ := maxFirst_mem _ hnonempty (halfLine_reach_bdd ω' (22 * N))
  have hv' : a + v ∈ openReachSet (topSites ω) (shiftedHalfLine a) (22 * N) :=
    (mem_openReachSet_translate (topSites ω) antidiagHalfLine a v (22 * N)).mp hv
  have hlev : shiftedHalfLine a ⊆ levelSet 0 := by
    rintro _ ⟨u, hu, rfl⟩
    have h := antidiagHalfLine_subset_levelSet hu
    change u.1 + u.2 = 0 at h
    simp only [levelSet, mem_ofPred_eq, a, traceSite, zero_add, Prod.fst_add, Prod.snd_add,
      Nat.cast_zero]
    omega
  obtain ⟨x, hx, hx0, hxf⟩ := exists_openTrace_of_reach hv' hlev
  have hxfst : x (22 * N) = b + halfLineEdge ω' (22 * N) := by
    have h := congrArg Prod.fst hxf
    have hvEdge : v.1 = halfLineEdge ω' (22 * N) := hve
    simpa only [a, traceSite, Prod.fst_add, zero_add, hvEdge] using h
  have hxEnd : 20 * (w : ℝ) < (traceRotation x (22 * N) : ℝ) := by
    unfold traceRotation
    rw [hxfst]
    push_cast
    unfold rotatedEdge at hterminal
    push_cast at hterminal
    linarith only [hterminal]
  have hxStart : x 0 ≤ b := by
    obtain ⟨u, hu, he⟩ := hx0
    have hu' := (show u.1 + u.2 = 0 ∧ u.1 ≤ 0 from hu).2
    have hx' := congrArg Prod.fst he
    simp only [a, traceSite, Prod.fst_add, zero_add] at hx'
    omega
  refine ⟨x, hx, fun n hn => ⟨?_, ?_⟩⟩
  · apply le_of_not_gt
    intro hbad
    exact hLeft ⟨x, hx, hxEnd, n, hn, hbad⟩
  · have hreach := traceRotation_le_shifted_edge hx
      (show 0 + n ≤ 22 * N by omega) b hxStart
    have hreach' : (traceRotation x n : ℝ) ≤ 2 * (b : ℝ) + rotatedEdge ω' n := by
      simpa only [Nat.zero_add, Nat.cast_zero, sub_zero] using hreach
    have herror := (abs_le.mp (hAt n hn)).2
    have hdiff : α - (w : ℝ) / (N : ℝ) ≤ 1 / (N : ℝ) := by
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN']
      simpa only [add_comm] using hfHi.le
    have hdiff' := mul_le_mul_of_nonneg_right hdiff (by positivity : (0 : ℝ) ≤ n)
    have hn' : (n : ℝ) ≤ 22 * (N : ℝ) := by exact_mod_cast hn
    have hratio : (n : ℝ) / (N : ℝ) ≤ 22 := (div_le_iff₀ hN').2 (by linarith only [hn'])
    have hdiff'' : α * (n : ℝ) - (w : ℝ) / (N : ℝ) * (n : ℝ) ≤ (n : ℝ) / (N : ℝ) := by
      calc
        _ = (α - (w : ℝ) / (N : ℝ)) * (n : ℝ) := by ring
        _ ≤ 1 / (N : ℝ) * (n : ℝ) := hdiff'
        _ = _ := by ring
    change (traceRotation x n : ℝ) ≤ (w : ℝ) / (N : ℝ) * (n : ℝ) - w
    linarith only [hw, hbHi, hreach', herror, hdiff'', hratio]

end LPPDifferentiability.FinalDraft.FlatBlockSource
