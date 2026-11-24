/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.ReachableLevel
import Differentiability.Model.Paths.DefectAlgebra
import Differentiability.Model.BackwardHeavyAttachmentNetGeometry
import Mathlib.Tactic

/-! The prescribed nets and middle-half reachability in Lemma B.3. -/

@[expose] public section

namespace LPPDifferentiability

/-- The transverse coordinate in the direction `(a, 1 - a)`. -/
def attachmentTransverse (a : ℝ) (z : Lattice) : ℝ :=
  (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)

/-- The gap and unique endpoint conditions for an increasing enumeration of a
prescribed net on level `I`. The extreme points can lie outside the interval
between the two endpoint thresholds. -/
def IsLevelAttachmentNet (a : ℝ) (m : ℕ) (I : ℤ) (A B : ℝ)
    {M : ℕ} (v : Fin (M + 1) → Lattice) : Prop :=
  let x := attachmentTransverse a ∘ v
  let g := min a (1 - a) * (m : ℝ) / 4
  (∀ j, (v j).1 + (v j).2 = I) ∧
  (∀ (j : ℕ) (hj : j < M),
    g ≤ x ⟨j + 1, by omega⟩ - x ⟨j, by omega⟩ ∧
    x ⟨j + 1, by omega⟩ - x ⟨j, by omega⟩ ≤ 2 * g) ∧
  (∀ j, (x j ≤ A + 2 * g ↔ j.val = 0)) ∧
  (∀ j, (B - 2 * g ≤ x j ↔ j.val = M))

/-- All interior net points lie between the endpoint thresholds. Summing
the lower gap bound over the interior indices controls the net size. -/
theorem IsLevelAttachmentNet.card_bound
    {a : ℝ} {m : ℕ} {I : ℤ} {A B : ℝ} {M : ℕ} {v : Fin (M + 1) → Lattice}
    (h : IsLevelAttachmentNet a m I A B v)
    (ha : 0 < a) (ha1 : a < 1) (hm : 0 < m) (hwidth : A ≤ B) :
    ((M + 1 : ℕ) : ℝ) ≤ 4 * (B - A) / (min a (1 - a) * (m : ℝ)) + 2 := by
  let x := attachmentTransverse a ∘ v
  let g := min a (1 - a) * (m : ℝ) / 4
  have hspec : (∀ (j : ℕ) (hj : j < M),
      g ≤ x ⟨j + 1, by omega⟩ - x ⟨j, by omega⟩) := fun j hj => (h.2.1 j hj).1
  have hg : 0 < g := by
    have htheta : 0 < min a (1 - a) := lt_min ha (sub_pos.mpr ha1)
    have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    dsimp [g]
    positivity
  have heq : 4 * (B - A) / (min a (1 - a) * (m : ℝ)) = (B - A) / g := by
    dsimp [g]
    rw [div_div_eq_mul_div, mul_comm (B - A)]
  rw [heq]
  have hmono : Monotone (fun j : Fin (M + 1) => x j - (j.val : ℝ) * g) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro j
    have hstep := hspec j.val j.isLt
    change x ⟨j.val, _⟩ - (j.val : ℝ) * g ≤
      x ⟨j.val + 1, _⟩ - ((j.val + 1 : ℕ) : ℝ) * g
    push_cast
    linarith only [hstep]
  by_cases hM : 2 ≤ M
  · let i : Fin (M + 1) := ⟨1, by omega⟩
    let j : Fin (M + 1) := ⟨M - 1, by omega⟩
    have hij : i ≤ j := by
      change 1 ≤ M - 1
      omega
    have hlow : A + 2 * g < x i := by
      apply lt_of_not_ge
      intro hx
      have hzero : i.val = 0 := (h.2.2.1 i).mp hx
      change 1 = 0 at hzero
      omega
    have hhigh : x j < B - 2 * g := by
      apply lt_of_not_ge
      intro hx
      have hlast : j.val = M := (h.2.2.2 j).mp hx
      change M - 1 = M at hlast
      omega
    have hspan := hmono hij
    change x i - ((1 : ℕ) : ℝ) * g ≤ x j - ((M - 1 : ℕ) : ℝ) * g at hspan
    simp only [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one] at hspan
    have hcard : ((M : ℝ) - 1) ≤ (B - A) / g := by
      apply (le_div_iff₀ hg).2
      linarith only [hlow, hhigh, hspan, hg]
    push_cast
    linarith only [hcard]
  · have hnonneg : 0 ≤ (B - A) / g := div_nonneg (sub_nonneg.mpr hwidth) hg.le
    have hcard : (((M + 1) : ℕ) : ℝ) ≤ 2 := by
      exact_mod_cast (show M + 1 ≤ 2 by omega)
    linarith only [hcard, hnonneg]

/-- Every starting site has a point of the prescribed upper net in the
middle half of its reachable interval. See the proof of (B.5). -/
theorem IsLevelAttachmentNet.exists_forward_middle
    {a : ℝ} {m : ℕ} {I : ℤ} {lo hi : ℝ} {M : ℕ} {v : Fin (M + 1) → Lattice}
    (h : IsLevelAttachmentNet a m (I + (m : ℤ))
      (lo - a * (m : ℝ)) (hi + (1 - a) * (m : ℝ)) v)
    (ha : 0 < a) (ha1 : a < 1) (hm : 0 < m) (u : Lattice)
    (hu : u.1 + u.2 = I) (hinterval : attachmentTransverse a u ∈ Set.Icc lo hi) :
    ∃ (j : Fin (M + 1)) (d : ℕ × ℕ),
      d.1 + d.2 = m ∧ u + ((d.1 : ℤ), (d.2 : ℤ)) = v j ∧
      (d.1 : ℝ) / (m : ℝ) ∈ Set.Icc (1 / 4) (3 / 4) ∧
      |attachmentTransverse a (v j - u)| ≤ (m : ℝ) := by
  classical
  let x := attachmentTransverse a ∘ v
  let r := attachmentTransverse a u
  let L := r - a * (m : ℝ) + (m : ℝ) / 4
  let U := r - a * (m : ℝ) + 3 * (m : ℝ) / 4
  let g := min a (1 - a) * (m : ℝ) / 4
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have htheta : min a (1 - a) ≤ (1 / 2 : ℝ) := by
    linarith only [min_le_left a (1 - a), min_le_right a (1 - a)]
  have hg : 0 ≤ 2 * g := by
    have hthetaPos := lt_min ha (sub_pos.mpr ha1)
    dsimp [g]
    positivity
  have hgsmall : 2 * g ≤ (m : ℝ) / 4 := by
    dsimp only [g]
    linarith only [mul_le_mul_of_nonneg_right htheta hmR.le]
  have hfirst : x ⟨0, by omega⟩ ≤ L := by
    have hleft : x ⟨0, by omega⟩ ≤ lo - a * (m : ℝ) + 2 * g := (h.2.2.1 _).mpr rfl
    have huLo : lo ≤ r := hinterval.1
    dsimp only [L]
    linarith only [hleft, huLo, hgsmall]
  have hlast : U ≤ x ⟨M, by omega⟩ := by
    have hright : hi + (1 - a) * (m : ℝ) - 2 * g ≤ x ⟨M, by omega⟩ :=
      (h.2.2.2 _).mpr rfl
    have huHi : r ≤ hi := hinterval.2
    dsimp only [U]
    linarith only [hright, huHi, hgsmall]
  have hlen : L + 2 * g ≤ U := by
    dsimp only [L, U]
    linarith only [hgsmall, hmR]
  obtain ⟨j, hjlo, hjhi⟩ := finite_grid_interval_coverage M x L U (2 * g)
    hg hlen hfirst hlast (fun k hk => (h.2.1 k hk).2)
  have hlevel : (v j).1 + (v j).2 = u.1 + u.2 + (m : ℤ) := by
    rw [hu]
    exact h.1 j
  have hfull : x j ∈ Set.Icc (r - a * (m : ℝ)) (r + (1 - a) * (m : ℝ)) := by
    dsimp only [L] at hjlo
    dsimp only [U] at hjhi
    exact ⟨by linarith only [hjlo, hmR], by linarith only [hjhi, hmR]⟩
  have hreachable := (forwardLevelInterval_iff u (v j) m a).2 ⟨hlevel, hfull⟩
  rcases Finset.mem_image.mp ((forwardReachable_mem_iff u (v j) m).2 hreachable) with
    ⟨k, -, hpoint⟩
  have hx : x j = r - a * (m : ℝ) + (k.val : ℝ) := by
    change attachmentTransverse a (v j) = _
    rw [← hpoint]
    exact forwardReachable_transverse u m k a
  have hklo : (m : ℝ) / 4 ≤ (k.val : ℝ) := by
    rw [hx] at hjlo
    dsimp only [L] at hjlo
    linarith only [hjlo]
  have hkhi : (k.val : ℝ) ≤ 3 * (m : ℝ) / 4 := by
    rw [hx] at hjhi
    dsimp only [U] at hjhi
    linarith only [hjhi]
  have hr : attachmentTransverse a (v j - u) = x j - r := by
    simpa only [attachmentTransverse, latticeTransverseCoordinate, transverseCoordinate,
      Function.comp_apply, x, r] using latticeTransverseCoordinate_sub a (v j) u
  refine ⟨j, (k.val, m - k.val), by omega, hpoint, ?_, ?_⟩
  · exact ⟨(le_div_iff₀ hmR).mpr (by linarith only [hklo]),
      (div_le_iff₀ hmR).mpr (by linarith only [hkhi])⟩
  · rw [hr, hx, abs_le]
    have ham : a * (m : ℝ) ≤ (m : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1.le hmR.le
    have ham0 : 0 ≤ a * (m : ℝ) := mul_nonneg ha.le hmR.le
    exact ⟨by linarith only [hklo, hmR, ham], by linarith only [hkhi, hmR, ham0]⟩

/-- Negating the sites and reversing the order of a prescribed lower net
gives the prescribed upper net for the reflected interval. -/
theorem IsLevelAttachmentNet.reflect
    {a : ℝ} {m : ℕ} {I : ℤ} {A B : ℝ} {M : ℕ} {v : Fin (M + 1) → Lattice}
    (h : IsLevelAttachmentNet a m I A B v) :
    IsLevelAttachmentNet a m (-I) (-B) (-A) (fun j => -v j.rev) := by
  let x := attachmentTransverse a ∘ v
  let g := min a (1 - a) * (m : ℝ) / 4
  have hneg (z : Lattice) : attachmentTransverse a (-z) = -attachmentTransverse a z :=
    backward_heavy_transverse_neg a z
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    have hj := h.1 j.rev
    simp only [Prod.fst_neg, Prod.snd_neg]
    omega
  · intro j hj
    let k := M - 1 - j
    have hk : k < M := by dsimp only [k]; omega
    have h₁ : (⟨j + 1, by omega⟩ : Fin (M + 1)).rev = ⟨k, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev, k]
      omega
    have h₂ : (⟨j, by omega⟩ : Fin (M + 1)).rev = ⟨k + 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev, k]
      omega
    have hh : g ≤ x ⟨k + 1, by omega⟩ - x ⟨k, by omega⟩ ∧
        x ⟨k + 1, by omega⟩ - x ⟨k, by omega⟩ ≤ 2 * g := h.2.1 k hk
    change g ≤ attachmentTransverse a (-v (⟨j + 1, _⟩ : Fin (M + 1)).rev) -
        attachmentTransverse a (-v (⟨j, _⟩ : Fin (M + 1)).rev) ∧
      attachmentTransverse a (-v (⟨j + 1, _⟩ : Fin (M + 1)).rev) -
        attachmentTransverse a (-v (⟨j, _⟩ : Fin (M + 1)).rev) ≤ 2 * g
    rw [hneg, hneg, h₁, h₂]
    change g ≤ -x ⟨k, _⟩ - -x ⟨k + 1, _⟩ ∧ -x ⟨k, _⟩ - -x ⟨k + 1, _⟩ ≤ 2 * g
    exact ⟨by linarith only [hh.1], by linarith only [hh.2]⟩
  · intro j
    change attachmentTransverse a (-v j.rev) ≤ -B + 2 * g ↔ j.val = 0
    rw [hneg]
    have hrev : j.rev.val = M ↔ j.val = 0 := by simp only [Fin.val_rev]; omega
    rw [← hrev, ← h.2.2.2 j.rev]
    change -x j.rev ≤ -B + 2 * g ↔ B - 2 * g ≤ x j.rev
    constructor <;> intro hx <;> linarith only [hx]
  · intro j
    change -A - 2 * g ≤ attachmentTransverse a (-v j.rev) ↔ j.val = M
    rw [hneg]
    have hrev : j.rev.val = 0 ↔ j.val = M := by simp only [Fin.val_rev]; omega
    rw [← hrev, ← h.2.2.1 j.rev]
    change -A - 2 * g ≤ -x j.rev ↔ x j.rev ≤ A + 2 * g
    constructor <;> intro hx <;> linarith only [hx]

/-- Every ending site has a point of the prescribed lower net in the
middle half of the window of possible starting sites. -/
theorem IsLevelAttachmentNet.exists_backward_middle
    {a : ℝ} {m : ℕ} {I : ℤ} {lo hi : ℝ} {M : ℕ} {v : Fin (M + 1) → Lattice}
    (h : IsLevelAttachmentNet a m (I - (m : ℤ))
      (lo - (1 - a) * (m : ℝ)) (hi + a * (m : ℝ)) v)
    (ha : 0 < a) (ha1 : a < 1) (hm : 0 < m) (u : Lattice)
    (hu : u.1 + u.2 = I) (hinterval : attachmentTransverse a u ∈ Set.Icc lo hi) :
    ∃ (j : Fin (M + 1)) (d : ℕ × ℕ),
      d.1 + d.2 = m ∧ v j + ((d.1 : ℤ), (d.2 : ℤ)) = u ∧
      (d.1 : ℝ) / (m : ℝ) ∈ Set.Icc (1 / 4) (3 / 4) ∧
      |attachmentTransverse a (u - v j)| ≤ (m : ℝ) := by
  let w : Fin (M + 1) → Lattice := fun j => -v j.rev
  have hw : IsLevelAttachmentNet a m (-I + (m : ℤ))
      (-hi - a * (m : ℝ)) (-lo + (1 - a) * (m : ℝ)) w := by
    have hI : -(I - (m : ℤ)) = -I + (m : ℤ) := by omega
    have hA : -(hi + a * (m : ℝ)) = -hi - a * (m : ℝ) := by ring
    have hB : -(lo - (1 - a) * (m : ℝ)) = -lo + (1 - a) * (m : ℝ) := by ring
    simpa only [hI, hA, hB] using h.reflect
  have hlevel : (-u).1 + (-u).2 = -I := by
    simp only [Prod.fst_neg, Prod.snd_neg]
    omega
  have hcoords : attachmentTransverse a (-u) ∈ Set.Icc (-hi) (-lo) := by
    have hneg : attachmentTransverse a (-u) = -attachmentTransverse a u :=
      backward_heavy_transverse_neg a u
    rw [hneg]
    exact ⟨by linarith only [hinterval.2], by linarith only [hinterval.1]⟩
  obtain ⟨j, d, hd, hend, hcentral, habs⟩ :=
    hw.exists_forward_middle ha ha1 hm (-u) hlevel hcoords
  have hendV : v j.rev + ((d.1 : ℤ), (d.2 : ℤ)) = u := by
    dsimp only [w] at hend
    apply Prod.ext
    · have hh := congrArg Prod.fst hend
      simp only [Prod.fst_add, Prod.fst_neg] at hh ⊢
      omega
    · have hh := congrArg Prod.snd hend
      simp only [Prod.snd_add, Prod.snd_neg] at hh ⊢
      omega
  have hsub : w j - -u = u - v j.rev := by
    dsimp only [w]
    abel
  exact ⟨j.rev, d, hd, hendV, hcentral, hsub ▸ habs⟩

end LPPDifferentiability
