/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.StairGeometry.Deterministic
public import Differentiability.Model.Paths.GridCoarseGeneralPieces
public import LPP_Foundations.Model.Paths.HorizontalFirst
public import LPP_Foundations.Frozen.Model.PathWeight
import LPP_Foundations.Model.Paths.Level
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic

/-! The streams of vertices in the final draft's selected staircase family. -/

@[expose] public section

namespace LPPDifferentiability.SelectedGridPaths

open StairGeometry Set
open scoped Classical

/-- A path with its starting site and displacement. -/
abbrev PackedPath := Σ u : Lattice, Σ d : ℕ × ℕ, Path u d

/-- The antidiagonal level of a vertex. -/
abbrev lev (z : Lattice) : ℤ := z.1 + z.2

/-- Real representatives of the Boolean very-bad mask, with cutoff zero. -/
noncomputable def maskEnvironment (b : Lattice → Bool) : Environment :=
  fun z => if b z then -1 else 0

/-- The mask obtained from the actual weights at the source cutoff. -/
noncomputable def siteMask (ω : Environment) (T : ℝ) : Lattice → Bool :=
  fun z => decide (ω z < -T)

theorem maskEnvironment_nonneg_iff (b : Lattice → Bool) (z : Lattice) :
    0 ≤ maskEnvironment b z ↔ b z = false := by
  cases h : b z <;> simp [maskEnvironment, h]

theorem siteMask_eq_false_iff (ω : Environment) (T : ℝ) (z : Lattice) :
    siteMask ω T z = false ↔ -T ≤ ω z := by
  simp [siteMask, not_lt]

theorem reachSet_mask (ω : Environment) (T : ℝ) (z : Lattice) :
    reachSet (maskEnvironment (siteMask ω T)) 0 z = reachSet ω T z := by
  ext y
  simp only [reachSet, Set.mem_ofPred_eq, neg_zero, maskEnvironment_nonneg_iff,
    siteMask_eq_false_iff]

theorem reachBackSet_mask (ω : Environment) (T : ℝ) (z : Lattice) :
    reachBackSet (maskEnvironment (siteMask ω T)) 0 z = reachBackSet ω T z := by
  ext y
  simp only [reachBackSet, Set.mem_ofPred_eq, neg_zero, maskEnvironment_nonneg_iff,
    siteMask_eq_false_iff]

theorem forwardTrapped_mask (ω : Environment) (T : ℝ) :
    forwardTrapped (maskEnvironment (siteMask ω T)) 0 = forwardTrapped ω T := by
  ext z
  simp only [forwardTrapped, Set.mem_ofPred_eq, reachSet_mask]

theorem backwardBlocked_mask (ω : Environment) (T : ℝ) :
    backwardBlocked (maskEnvironment (siteMask ω T)) 0 = backwardBlocked ω T := by
  have hb (z : Lattice) :
      maskEnvironment (siteMask ω T) z < 0 ↔ ω z < -T := by
    rw [← not_le, maskEnvironment_nonneg_iff, siteMask_eq_false_iff, not_le]
  ext z
  simp only [backwardBlocked, Set.mem_ofPred_eq, neg_zero, hb, reachBackSet_mask]

/-- The forward greedy stream. A selector using this stream checks the start and region. -/
noncomputable def forwardStream (b : Lattice → Bool) (a : ℝ) (u : Lattice) : ℕ → Lattice :=
  GreedyAttachment.vertex u a (forwardTrapped (maskEnvironment b) 0)

/-- The backward stream, in physical coordinates and counted backward from its origin. -/
noncomputable def backwardStream (b : Lattice → Bool) (a : ℝ) (u : Lattice) (n : ℕ) : Lattice :=
  -GreedyAttachment.vertex (-u) a {z | -z ∈ backwardBlocked (maskEnvironment b) 0} n

/-- The vertex of the staircase through `u` on a covered level. -/
noncomputable def gammaPoint (b : Lattice → Bool) (a : ℝ) (u : Lattice) (I : ℤ) : Lattice :=
  if lev u ≤ I then forwardStream b a u (I - lev u).toNat
  else backwardStream b a u (lev u - I).toNat

theorem gammaPoint_eq_forward (b : Lattice → Bool) (a : ℝ) (u : Lattice) (I : ℤ)
    (hI : lev u ≤ I) : gammaPoint b a u I = forwardStream b a u (I - lev u).toNat :=
  ite_eq_left hI

theorem gammaPoint_eq_backward (b : Lattice → Bool) (a : ℝ) (u : Lattice) (I : ℤ)
    (hI : I ≤ lev u) : gammaPoint b a u I = backwardStream b a u (lev u - I).toNat := by
  rcases eq_or_lt_of_le hI with rfl | h
  · simp [gammaPoint, forwardStream, backwardStream, GreedyAttachment.vertex_zero]
  · exact ite_eq_right h.not_ge

theorem gammaPoint_level (b : Lattice → Bool) (a : ℝ) (u : Lattice) (I : ℤ) :
    lev (gammaPoint b a u I) = I := by
  rcases le_total (lev u) I with hI | hI
  · rw [gammaPoint_eq_forward _ _ _ _ hI]
    unfold forwardStream lev
    change u.1 + u.2 ≤ I at hI
    rw [GreedyAttachment.level, Int.toNat_of_nonneg (sub_nonneg.mpr hI)]
    omega
  · rw [gammaPoint_eq_backward _ _ _ _ hI]
    unfold backwardStream lev
    simp only [Prod.fst_neg, Prod.snd_neg]
    change I ≤ u.1 + u.2 at hI
    have hl := GreedyAttachment.level (-u) a
      {z | -z ∈ backwardBlocked (maskEnvironment b) 0} (u.1 + u.2 - I).toNat
    simp only [Prod.fst_neg, Prod.snd_neg, Int.toNat_of_nonneg (sub_nonneg.mpr hI)] at hl
    omega

theorem gammaPoint_step (b : Lattice → Bool) (a : ℝ) (u : Lattice) (I : ℤ) :
    gammaPoint b a u (I + 1) = gammaPoint b a u I + (1, 0) ∨
      gammaPoint b a u (I + 1) = gammaPoint b a u I + (0, 1) := by
  by_cases h : lev u ≤ I
  · rw [gammaPoint_eq_forward b a u I h, gammaPoint_eq_forward b a u (I + 1) (by omega),
      show (I + 1 - lev u).toNat = (I - lev u).toNat + 1 by omega]
    exact GreedyAttachment.step u a _ _
  · rw [gammaPoint_eq_backward b a u (I + 1) (by omega),
      gammaPoint_eq_backward b a u I (by omega)]
    let i := (lev u - (I + 1)).toNat
    rw [show (lev u - I).toNat = i + 1 by dsimp only [i]; omega]
    unfold backwardStream
    rcases GreedyAttachment.step (-u) a {z | -z ∈ backwardBlocked (maskEnvironment b) 0} i with he | hn
    · left
      rw [he]
      abel
    · right
      rw [hn]
      abel

/-- The indicated level is covered by an available part of the greedy staircase.
The whole part between `u` and that level must have stayed inside the region. -/
def gammaDefined (Q : Set Lattice) (b : Lattice → Bool) (a : ℝ) (u : Lattice) (I : ℤ) : Prop :=
  (lev u ≤ I ∧ u ∉ forwardTrapped (maskEnvironment b) 0 ∧
    ∀ s ≤ (I - lev u).toNat, forwardStream b a u s ∈ Q) ∨
  (I ≤ lev u ∧ u ∉ backwardBlocked (maskEnvironment b) 0 ∧
    ∀ s ≤ (lev u - I).toNat, backwardStream b a u s ∈ Q)

/-- The literal vertices of the fine segment, including its terminal vertex. -/
noncomputable def gammaStream (b : Lattice → Bool) (a : ℝ) (u : Lattice) (I : ℤ) (s : ℕ) :
    Lattice := gammaPoint b a u (I + (s : ℤ))

/-- The arriving stream follows the greedy prefix to the lower arrival box
and then the horizontal-first tail. Its specified length is `lev v - lev z`. -/
noncomputable def arrivalStream (b : Lattice → Bool) (L : ℕ) (z v : Lattice) (s : ℕ) : Lattice :=
  let n := (lev v - lev z).toNat
  let x := forwardStream b (((v.1 - z.1 : ℤ) : ℝ) / n) z
  let p := x (n - L)
  let e : ℕ × ℕ := ((v.1 - p.1).toNat, (v.2 - p.2).toNat)
  if s ≤ n - L then x s
  else
    let j := s - (n - L)
    p + (Int.ofNat (min j e.1), Int.ofNat (j - e.1))

/-- The stream from the trimmed end aims at the source transverse coordinate
`r(u) - 2 Δ₀ - 3` on the terminal grid level. -/
noncomputable def mergeStream (b : Lattice → Bool) (a : ℝ) (Δ₀ : ℕ)
    (u v : Lattice) (Λ : ℤ) : ℕ → Lattice :=
  forwardStream b ((transverse a u - 2 * (Δ₀ : ℝ) - 3 + a * (Λ : ℝ) - (v.1 : ℝ)) /
    ((Λ - lev v : ℤ) : ℝ)) v

/-- The first meeting with a defined vertex of the staircase, up through the
terminal level. Failure to meet gives no index and contributes no path. -/
noncomputable def firstMeeting (Q : Set Lattice) (b : Lattice → Bool) (a : ℝ) (Δ₀ : ℕ)
    (u v : Lattice) (Λ : ℤ) : Option ℕ :=
  let P (i : ℕ) := i ≤ (Λ - lev v).toNat ∧
    gammaDefined Q b a u (lev v + (i : ℤ)) ∧
    mergeStream b a Δ₀ u v Λ i = gammaStream b a u (lev v) i
  if h : ∃ i, P i then some (Nat.find h) else none

/-- All actual vertices are in the region and all collected sites avoid the mask. -/
def admissibleIn (Q : Set Lattice) (b : Lattice → Bool) (y : ℕ → Lattice) (n : ℕ) : Prop :=
  (∀ i < n, y (i + 1) = y i + (1, 0) ∨ y (i + 1) = y i + (0, 1)) ∧
  (∀ i ≤ n, y i ∈ Q) ∧ ∀ i < n, b (y i) = false

/-- The path given by a stream with verified up-right steps. -/
noncomputable def packStream (y : ℕ → Lattice) (n : ℕ)
    (h : ∀ i < n, y (i + 1) = y i + (1, 0) ∨ y (i + 1) = y i + (0, 1)) : PackedPath :=
  let p := exists_path_of_seq y n h
  ⟨y 0, p.choose, p.choose_spec.choose⟩

/-- An actual path selected from its stream, with no entry for an undefined
or inadmissible stream. The terminal vertex is checked for region membership. -/
noncomputable def checkedPath (Q : Set Lattice) (b : Lattice → Bool) (y : ℕ → Lattice) (n : ℕ) :
    Option PackedPath :=
  if h : admissibleIn Q b y n then some (packStream y n h.1) else none

/-- The selected path is determined by the supplied stream on its full length. -/
theorem checkedPath_spec {Q : Set Lattice} {b : Lattice → Bool} {y : ℕ → Lattice}
    {n : ℕ} {q : PackedPath} (h : checkedPath Q b y n = some q) :
    admissibleIn Q b y n ∧ q.1 = y 0 ∧ q.2.1.1 + q.2.1.2 = n ∧
      (∀ i, q.2.2.vertex i = y i.val) ∧
      ∀ ω : Environment, pathWeight ω q.2.2 = ∑ i ∈ Finset.range n, ω (y i) := by
  unfold checkedPath at h
  split at h
  · rename_i hy
    cases h
    have hp := (exists_path_of_seq y n hy.1).choose_spec.choose_spec
    exact ⟨hy, rfl, hp.2.1, hp.2.2.1, hp.2.2.2⟩
  · cases h

/-- An admissible stream contributes its actual path. -/
theorem checkedPath_exists {Q : Set Lattice} {b : Lattice → Bool} {y : ℕ → Lattice}
    {n : ℕ} (h : admissibleIn Q b y n) : ∃ q, checkedPath Q b y n = some q :=
  ⟨packStream y n h.1, dite_eq_left h⟩

/-- The path selectors have genuine in-region and very-bad-free outputs. -/
theorem checkedPath_region_mask {Q : Set Lattice} {b : Lattice → Bool} {y : ℕ → Lattice}
    {n : ℕ} {q : PackedPath} (h : checkedPath Q b y n = some q) :
    (∀ i, q.2.2.vertex i ∈ Q) ∧ (∀ i : Fin (q.2.1.1 + q.2.1.2), b (q.2.2.vertex i.castSucc) = false) := by
  obtain ⟨ha, -, hn, hv, -⟩ := checkedPath_spec h
  exact ⟨fun i => by rw [hv]; exact ha.2.1 _ (by have := i.isLt; omega),
    fun i => by rw [hv]; exact ha.2.2 _ (by have := i.isLt; simp only [Fin.val_castSucc]; omega)⟩

end LPPDifferentiability.SelectedGridPaths
