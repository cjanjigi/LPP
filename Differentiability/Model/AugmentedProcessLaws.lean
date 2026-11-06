/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.OrientedPercolation
import Differentiability.Model.OrientedPercolationLaws
import Differentiability.Model.PercolationTriangles
import Differentiability.Probability.HalfLineEdge
import Differentiability.Probability.RightBlockGain
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Pathwise laws of the augmented process

Statements about the augmented process that hold for every environment, before any
probability is used:

* `isTriangle_translate`: the triangle at `r` in a translated environment is the triangle at
  the translated site;
* `openReachSet_subset_augmentedProcess`: the occupied set contains the plain open-path growth;
* `augmentedProcess_fst_le`, `augmentedProcess_count_le`, `openEdge_augmentedProcess_le`:
  bounds on the first coordinates, on the counter and on the edge;
* `openEdge_triangle_gain_ge`: the pathwise part of the freezing lemma. After translating by
  the corner of the triangle moved up by `T`, the random occupied set disappears and the gain
  from adding the targets is at least the gain for the half-line.

Block indices are variables in every induction here, so the one-step law of the process is
proved once (`step_cases`) and reused.

## References

- Georgiou, Rassoul-Agha and Seppäläinen (manuscript in preparation), the endpoint
  differentiability argument.
-/

@[expose] public section

namespace LPPDifferentiability

open Set

/-! ## Auxiliary lemmas -/

/-- One step of the process: either the next set is the plain open-path growth and the counter
is unchanged, or the guard held and the targets were added and the counter went up by one. -/
private theorem step_cases (ω : Environment) (T : ℕ) (c₀ : ℝ) (S : Set Lattice) (k j : ℕ) :
    ((augmentedProcess ω T c₀ S k (j + 1)).1 =
        openReachSet (topSites ω) (augmentedProcess ω T c₀ S k j).1 T ∧
      (augmentedProcess ω T c₀ S k (j + 1)).2 = (augmentedProcess ω T c₀ S k j).2) ∨
    (∃ r : Lattice, r ∈ (augmentedProcess ω T c₀ S k j).1 ∧ IsTriangle ω T c₀ r ∧
      (augmentedProcess ω T c₀ S k j).2 < k ∧
      (augmentedProcess ω T c₀ S k (j + 1)).1 =
        openReachSet (topSites ω) (augmentedProcess ω T c₀ S k j).1 T ∪ triangleTargets T r ∧
      (augmentedProcess ω T c₀ S k (j + 1)).2 = (augmentedProcess ω T c₀ S k j).2 + 1) := by
  simp only [augmentedProcess]
  split_ifs with h
  · exact Or.inr ⟨_, h.2.1, h.2.2, h.1, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

/-- The edge of a set whose first coordinates are at most `b ≥ 0` is at most `b + m`. -/
private theorem openEdge_le_of_fst_le (O X : Set Lattice) (b : ℤ) (hb0 : 0 ≤ b)
    (hb : ∀ v ∈ X, v.1 ≤ b) (m : ℕ) : openEdge O X m ≤ b + m := by
  by_cases hne : (openReachSet O X m).Nonempty
  · have hbdd : BddAbove (Prod.fst '' openReachSet O X m) := by
      refine ⟨b + m, ?_⟩
      rintro _ ⟨v, hv, rfl⟩
      exact bddAbove_fst_openReachSet O X m b hb v hv
    obtain ⟨v, hv, hvv⟩ := maxFirst_mem _ hne hbdd
    have h1 : openEdge O X m = v.1 := hvv.symm
    have h2 := bddAbove_fst_openReachSet O X m b hb v hv
    rw [h1]
    exact h2
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : openEdge O X m = 0 := by
      unfold openEdge maxFirst
      rw [hne, Set.image_empty, Int.csSup_empty]
    rw [h0]
    have hm : (0 : ℤ) ≤ m := by positivity
    linarith

/-! ## Translation of the triangle -/

/-- The triangle at `r` for the environment seen from `t` is the triangle at `t + r` for the
original environment. This translation identity is used when comparing triangle events at
different sites. -/
theorem isTriangle_translate (ω : Environment) (T : ℕ) (c₀ : ℝ) (t r : Lattice) :
    IsTriangle (fun z => ω (t + z)) T c₀ r ↔ IsTriangle ω T c₀ (t + r) := by
  have e1 : ∀ i : ℕ, t + (r.1, r.2 + (i : ℤ)) = ((t + r).1, (t + r).2 + (i : ℤ)) := by
    intro i
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]
    · simp only [Prod.snd_add]; omega
  have e2 : t + (r.1 + 1, r.2) = ((t + r).1 + 1, (t + r).2) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]; omega
    · simp only [Prod.snd_add]
  unfold IsTriangle
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i hi1 hi2 => ?_, ?_, fun z hz1 hz2 hz3 hz4 => ?_⟩
    · simpa only [e1 i] using h1 i hi1 hi2
    · simpa only [e2] using h2
    · simp only [Prod.fst_add, Prod.snd_add] at hz1 hz2 hz3
      have hz4' : -t + z ≠ (r.1 + 1, r.2) := by
        intro h
        apply hz4
        calc z = t + (-t + z) := (add_neg_cancel_left t z).symm
          _ = t + (r.1 + 1, r.2) := by rw [h]
          _ = ((t + r).1 + 1, (t + r).2) := e2
      have key := h3 (-t + z)
        (by simp only [Prod.fst_add, Prod.fst_neg]; omega)
        (by simp only [Prod.snd_add, Prod.snd_neg]; omega)
        (by simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]; omega)
        hz4'
      simpa only [add_neg_cancel_left] using key
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i hi1 hi2 => ?_, ?_, fun z hz1 hz2 hz3 hz4 => ?_⟩
    · simpa only [e1 i] using h1 i hi1 hi2
    · simpa only [e2] using h2
    · have hz4' : t + z ≠ ((t + r).1 + 1, (t + r).2) := by
        intro h
        apply hz4
        rw [← e2] at h
        exact add_left_cancel h
      exact h3 (t + z)
        (by simp only [Prod.fst_add]; omega)
        (by simp only [Prod.snd_add]; omega)
        (by simp only [Prod.fst_add, Prod.snd_add]; omega)
        hz4'

/-! ## Laws of the augmented process -/

/-- The occupied set after `j` blocks contains the plain open-path growth from the start set,
because augmenting only adds sites. -/
theorem openReachSet_subset_augmentedProcess (ω : Environment) (T : ℕ) (c₀ : ℝ)
    (S : Set Lattice) (k j : ℕ) :
    openReachSet (topSites ω) S (j * T) ⊆ (augmentedProcess ω T c₀ S k j).1 := by
  induction j with
  | zero =>
    intro v hv
    rw [Nat.zero_mul, openReachSet_zero] at hv
    rw [augmentedProcess]
    exact hv
  | succ j ih =>
    intro v hv
    have e : (j + 1) * T = j * T + T := Nat.succ_mul j T
    rw [e, ← openReachSet_add] at hv
    have hmono : v ∈ openReachSet (topSites ω) (augmentedProcess ω T c₀ S k j).1 T :=
      openReachSet_mono (subset_refl _) ih T hv
    rcases step_cases ω T c₀ S k j with ⟨h1, -⟩ | ⟨r, -, -, -, h1, -⟩
    · rw [h1]
      exact hmono
    · rw [h1]
      exact Set.mem_union_left _ hmono

/-- If the start set has first coordinates at most `b`, the occupied set after `j` blocks has
first coordinates at most `b + jT`: an open block moves at most `T` to the right, and so do
the targets. -/
theorem augmentedProcess_fst_le (ω : Environment) (T : ℕ) (c₀ : ℝ) (S : Set Lattice)
    (b : ℤ) (hS : ∀ u ∈ S, u.1 ≤ b) (k j : ℕ) :
    ∀ v ∈ (augmentedProcess ω T c₀ S k j).1, v.1 ≤ b + (j : ℤ) * T := by
  induction j with
  | zero =>
    intro v hv
    rw [augmentedProcess] at hv
    have h := hS v hv
    have h0 : ((0 : ℕ) : ℤ) * (T : ℤ) = 0 := by simp
    linarith
  | succ j ih =>
    intro v hv
    have hopen : ∀ w ∈ openReachSet (topSites ω) (augmentedProcess ω T c₀ S k j).1 T,
        w.1 ≤ b + ((j + 1 : ℕ) : ℤ) * T := by
      intro w hw
      have h := bddAbove_fst_openReachSet (topSites ω) _ T (b + (j : ℤ) * T) ih w hw
      push_cast
      linarith
    rcases step_cases ω T c₀ S k j with ⟨h1, -⟩ | ⟨r, hrX, -, -, h1, -⟩
    · rw [h1] at hv
      exact hopen v hv
    · rw [h1] at hv
      rcases hv with hv | hv
      · exact hopen v hv
      · obtain ⟨-, -, h3⟩ : v.1 + v.2 = r.1 + r.2 + T ∧ r.1 + 1 ≤ v.1 ∧ v.1 ≤ r.1 + T := hv
        have h4 := ih r hrX
        push_cast
        linarith

/-- After `j` blocks the counter is at most `j` (one test per block) and at most the cap `k`. -/
theorem augmentedProcess_count_le (ω : Environment) (T : ℕ) (c₀ : ℝ) (S : Set Lattice)
    (k j : ℕ) :
    (augmentedProcess ω T c₀ S k j).2 ≤ j ∧ (augmentedProcess ω T c₀ S k j).2 ≤ k := by
  induction j with
  | zero =>
    have h0 : augmentedProcess ω T c₀ S k 0 = (S, 0) := by rw [augmentedProcess]
    rw [h0]
    exact ⟨Nat.le_refl _, Nat.zero_le _⟩
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rcases step_cases ω T c₀ S k j with ⟨-, h2⟩ | ⟨r, -, -, hK, -, h2⟩
    · constructor <;> omega
    · constructor <;> omega

/-- The edge of the occupied set after `j` blocks and `m` further levels is at most `jT + m`,
for a start set inside the half-line. It follows from the first-coordinate bound above. -/
theorem openEdge_augmentedProcess_le (ω : Environment) (T : ℕ) (c₀ : ℝ) (A : Set Lattice)
    (hA : A ⊆ antidiagHalfLine) (k j m : ℕ) :
    openEdge (topSites ω) (augmentedProcess ω T c₀ A k j).1 m ≤ (j : ℤ) * T + m := by
  have hA' : ∀ u ∈ A, u.1 ≤ 0 := fun u hu =>
    (show u.1 + u.2 = 0 ∧ u.1 ≤ 0 from hA hu).2
  refine openEdge_le_of_fst_le (topSites ω) _ ((j : ℤ) * T) (by positivity) ?_ m
  intro v hv
  have h := augmentedProcess_fst_le ω T c₀ A 0 hA' k j v hv
  linarith

/-! ## The freezing lemma, pathwise part -/

/-- The freezing lemma, pathwise part. If there is a triangle at `r` and every site of `X`
lies on the level of `r` weakly to its left, then adding the targets to the open growth of
`X` after `T` levels raises the edge, `m` levels later, by at least the gain of adding the
right block to the half-line in the environment translated by `r + (0, T)`. The translation
removes the random occupied set before any probability is used. The proof combines the blocking
property of the triangle with the pathwise gain inequality of the oriented-percolation gain
lemma of Georgiou, Rassoul-Agha and Seppäläinen (manuscript in preparation). -/
theorem openEdge_triangle_gain_ge (ω : Environment) (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ)
    (r : Lattice) (hr : IsTriangle ω T c₀ r) (X : Set Lattice)
    (hX : ∀ x ∈ X, x.1 + x.2 = r.1 + r.2 ∧ x.1 ≤ r.1) (m : ℕ)
    (hne : (openReachSet (topSites ω) X (T + m)).Nonempty) :
    openEdge (topSites (fun z => ω ((r.1, r.2 + (T : ℤ)) + z)))
        (antidiagHalfLine ∪ antidiagRightBlock T) m -
      halfLineEdge (fun z => ω ((r.1, r.2 + (T : ℤ)) + z)) m ≤
    openEdge (topSites ω) (openReachSet (topSites ω) X T ∪ triangleTargets T r) m -
      openEdge (topSites ω) (openReachSet (topSites ω) X T) m := by
  obtain ⟨t, ht⟩ : ∃ t : Lattice, t = (r.1, r.2 + (T : ℤ)) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Set Lattice, Y = openReachSet (topSites ω) X T := ⟨_, rfl⟩
  rw [← ht, ← hY]
  have ht1 : t.1 = r.1 := by
    have h := congrArg Prod.fst ht
    exact h
  have ht2 : t.2 = r.2 + (T : ℤ) := by
    have h := congrArg Prod.snd ht
    exact h
  have hsurj : Function.Surjective (fun z : Lattice => t + z) :=
    fun v => ⟨-t + v, add_neg_cancel_left t v⟩
  obtain ⟨A, hA⟩ : ∃ A : Set Lattice, A = (fun z : Lattice => t + z) ⁻¹' Y := ⟨_, rfl⟩
  have himg : (fun z : Lattice => t + z) '' A = Y := by
    rw [hA]
    exact Set.image_preimage_eq Y hsurj
  have htg : triangleTargets T r = (fun z : Lattice => t + z) '' antidiagRightBlock T := by
    rw [ht]
    exact triangleTargets_eq T r
  have hXlev : X ⊆ levelSet (r.1 + r.2) := fun x hx => (hX x hx).1
  have hYlev : Y ⊆ levelSet (r.1 + r.2 + (T : ℤ)) := by
    rw [hY]
    exact openReachSet_subset_levelSet (topSites ω) X (r.1 + r.2) T hXlev
  have hYleft : ∀ v ∈ Y, v.1 ≤ r.1 - 1 := by
    rw [hY]
    exact openReachSet_left_of_triangle ω T hT c₀ r hr X hX
  have hAsub : A ⊆ antidiagHalfLine := by
    intro z hz
    have hz' : t + z ∈ Y := by
      rw [hA] at hz
      exact hz
    have hl : (t + z).1 + (t + z).2 = r.1 + r.2 + (T : ℤ) := hYlev hz'
    have hle : (t + z).1 ≤ r.1 - 1 := hYleft _ hz'
    simp only [Prod.fst_add, Prod.snd_add] at hl hle
    show z.1 + z.2 = 0 ∧ z.1 ≤ 0
    constructor <;> omega
  have hbA : BddAbove (Prod.fst '' A) := bddAbove_fst_antidiagHalfLine.mono (Set.image_mono hAsub)
  have hbF := bddAbove_fst_antidiagRightBlock T
  have hbAF : BddAbove (Prod.fst '' (A ∪ antidiagRightBlock T)) := by
    rw [Set.image_union]
    exact hbA.union hbF
  have hneY : (openReachSet (topSites ω) Y m).Nonempty := by
    rw [hY, openReachSet_add]
    exact hne
  have hneU : (openReachSet (topSites ω) (Y ∪ triangleTargets T r) m).Nonempty :=
    hneY.mono (openReachSet_mono (subset_refl _) Set.subset_union_left m)
  have hU : (fun z : Lattice => t + z) '' (A ∪ antidiagRightBlock T) =
      Y ∪ triangleTargets T r := by
    rw [Set.image_union, himg, htg]
  have hneA : (openReachSet (topSites fun z => ω (t + z)) A m).Nonempty := by
    obtain ⟨x, hx⟩ := hneY
    refine ⟨-t + x, ?_⟩
    have hx' : x ∈ openReachSet (topSites ω) ((fun z : Lattice => t + z) '' A) m := by
      rw [himg]
      exact hx
    exact (mem_openReachSet_translate (topSites ω) A t (-t + x) m).2
      (by rw [add_neg_cancel_left]; exact hx')
  have hE1 : openEdge (topSites ω) Y m =
      t.1 + openEdge (topSites fun z => ω (t + z)) A m := by
    have h := openEdge_translate ω A t m (by rw [himg]; exact hneY) hbA
    rw [himg] at h
    exact h
  have hE2 : openEdge (topSites ω) (Y ∪ triangleTargets T r) m =
      t.1 + openEdge (topSites fun z => ω (t + z)) (A ∪ antidiagRightBlock T) m := by
    have h := openEdge_translate ω (A ∪ antidiagRightBlock T) t m
      (by rw [hU]; exact hneU) hbAF
    rw [hU] at h
    exact h
  have hmain := openEdge_union_gain_antitone (topSites fun z => ω (t + z)) A
    antidiagHalfLine (antidiagRightBlock T) m hAsub hneA bddAbove_fst_antidiagHalfLine hbF
  unfold halfLineEdge
  rw [hE1, hE2]
  omega

end LPPDifferentiability
