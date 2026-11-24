/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.Model.OrientedPercolationLaws
import LPP_Foundations.Model.Paths.Level
import Mathlib.Tactic

/-! Physical paths and their intersections for Durrett (1984), Figure 7. -/

@[expose] public section

open Set

namespace LPPDifferentiability.FinalDraft.FlatBlockSource

/-- Express a site above an anchor by its relative level and first coordinate. -/
def traceSite (a : Lattice) (t : ℕ) (x : ℤ) : Lattice :=
  a + (x, (t : ℤ) - x)

/-- The first coordinate of a directed path increases by zero or one. -/
def TraceSteps (n : ℕ) (x : ℕ → ℤ) : Prop :=
  ∀ i < n, x (i + 1) = x i ∨ x (i + 1) = x i + 1

/-- A site crossing requires openness at every arrival. Its initial vertex is free,
as in the repository's `OpenReach` site model. -/
def OpenTrace (ω : Environment) (a : Lattice) (n : ℕ) (x : ℕ → ℤ) : Prop :=
  TraceSteps n x ∧ ∀ i < n, ω (traceSite a (i + 1) (x (i + 1))) = 1

/-- At a fixed level, reflection interchanges the two lattice coordinates. -/
def reflectTrace (x : ℕ → ℤ) (t : ℕ) : ℤ := (t : ℤ) - x t

/-- The first-coordinate displacement is between zero and the elapsed time. -/
theorem TraceSteps.displacement {n : ℕ} {x : ℕ → ℤ} (hx : TraceSteps n x)
    (s r : ℕ) (hr : s + r ≤ n) :
    0 ≤ x (s + r) - x s ∧ x (s + r) - x s ≤ (r : ℤ) := by
  induction r with
  | zero => simp
  | succ r ih =>
      obtain ⟨hl, hu⟩ := ih (by omega)
      rcases hx (s + r) (by omega) with h | h <;>
        rw [Nat.add_succ, Nat.cast_succ, h] <;> omega

/-- Figure 7's opposite endpoint orders force an actual common first coordinate. -/
theorem traces_meet {n m a b r : ℕ} {x y : ℕ → ℤ} {u v : ℤ}
    (hx : TraceSteps n x) (hy : TraceSteps m y)
    (hna : a + r ≤ n) (hmb : b + r ≤ m)
    (hstart : u + x a ≤ v + y b)
    (hend : v + y (b + r) ≤ u + x (a + r)) :
    ∃ j ≤ r, u + x (a + j) = v + y (b + j) := by
  induction r with
  | zero => exact ⟨0, le_rfl, le_antisymm (by simpa using hstart) hend⟩
  | succ r ih =>
      by_cases h : v + y (b + r) ≤ u + x (a + r)
      · obtain ⟨j, hj, he⟩ := ih (by omega) (by omega) h
        exact ⟨j, hj.trans (Nat.le_succ _), he⟩
      · have h' : v + y (b + r + 1) ≤ u + x (a + r + 1) := by
          simpa only [Nat.add_succ] using hend
        have hle : u + x (a + r + 1) ≤ v + y (b + r + 1) := by
          rcases hx (a + r) (by omega) with hx' | hx' <;>
            rcases hy (b + r) (by omega) with hy' | hy' <;> omega
        exact ⟨r + 1, le_rfl, by simpa only [Nat.add_succ] using le_antisymm hle h'⟩

/-- First coordinate and level determine the physical vertex at a crossing contact. -/
theorem traceSite_eq_of_level_fst {a b : Lattice} {s t : ℕ} {x y : ℤ}
    (hl : a.1 + a.2 + (s : ℤ) = b.1 + b.2 + (t : ℤ))
    (hf : a.1 + x = b.1 + y) : traceSite a s x = traceSite b t y := by
  apply Prod.ext
  · exact hf
  · simp only [traceSite, Prod.snd_add]
    omega

/-- The part between any two times is actual open reachability. -/
theorem OpenTrace.segment {ω : Environment} {a : Lattice} {n : ℕ} {x : ℕ → ℤ}
    (hx : OpenTrace ω a n x) (s r : ℕ) (hr : s + r ≤ n) :
    traceSite a (s + r) (x (s + r)) ∈
      openReachSet (topSites ω) {traceSite a s (x s)} r := by
  obtain ⟨hl, hu⟩ := hx.1.displacement s r hr
  let e : ℕ := (x (s + r) - x s).toNat
  have he : (e : ℤ) = x (s + r) - x s := Int.toNat_of_nonneg hl
  have her : e ≤ r := by omega
  let d : ℕ × ℕ := (e, r - e)
  have hd : d.1 + d.2 = r := by dsimp [d]; omega
  have hend : traceSite a s (x s) + ((d.1 : ℤ), (d.2 : ℤ)) =
      traceSite a (s + r) (x (s + r)) := by
    apply Prod.ext <;>
      simp only [traceSite, d, Prod.fst_add, Prod.snd_add, Nat.cast_add, Nat.cast_sub her] <;> omega
  let p : Path (traceSite a s (x s)) d := {
    vertex := fun i => traceSite a (s + i.val) (x (s + i.val))
    start := by simp
    finish := by simpa only [Fin.val_last, hd] using hend.symm
    step := fun i => by
      have hi : i.val < r := by simpa only [hd] using i.isLt
      rcases hx.1 (s + i.val) (by omega) with h | h
      · right
        apply Prod.ext <;> simp only [traceSite, Fin.val_succ, Fin.val_castSucc,
          Prod.fst_add, Prod.snd_add, Nat.cast_add, Nat.cast_one, ← Nat.add_assoc] <;> omega
      · left
        apply Prod.ext <;> simp only [traceSite, Fin.val_succ, Fin.val_castSucc,
          Prod.fst_add, Prod.snd_add, Nat.cast_add, Nat.cast_one, ← Nat.add_assoc] <;> omega }
  refine ⟨traceSite a s (x s), rfl, ⟨d, hend, p, ?_⟩, ?_⟩
  · intro i
    have hi : i.val < r := by simpa only [hd] using i.isLt
    change ω (traceSite a (s + (i.val + 1)) (x (s + (i.val + 1)))) = 1
    rw [← Nat.add_assoc]
    exact hx.2 (s + i.val) (by omega)
  · simp only [traceSite, Prod.fst_add, Prod.snd_add, Nat.cast_add]
    omega

/-- A vertex reached from level zero gives an actual open trace. -/
theorem exists_openTrace_of_reach {ω : Environment} {S : Set Lattice} {n : ℕ}
    {v : Lattice} (hv : v ∈ openReachSet (topSites ω) S n) (hS : S ⊆ levelSet 0) :
    ∃ x : ℕ → ℤ, OpenTrace ω 0 n x ∧ traceSite 0 0 (x 0) ∈ S ∧ traceSite 0 n (x n) = v := by
  obtain ⟨u, hu, ⟨d, hd, p, hp⟩, hlev⟩ := hv
  have hu0 : u.1 + u.2 = 0 := hS hu
  have hd1 := congrArg Prod.fst hd
  have hd2 := congrArg Prod.snd hd
  simp only [Prod.fst_add, Prod.snd_add] at hd1 hd2
  have hn : d.1 + d.2 = n := by omega
  let ix (i : ℕ) : Fin (d.1 + d.2 + 1) := ⟨min i n, by omega⟩
  let x (i : ℕ) : ℤ := (p.vertex (ix i)).1
  have hx (i : ℕ) (hi : i ≤ n) : traceSite 0 i (x i) = p.vertex (ix i) := by
    have h := p.level (ix i)
    have hix : (ix i).val = i := min_eq_left hi
    rw [hix, hu0, zero_add] at h
    apply Prod.ext
    · simp only [traceSite, x, zero_add]
    · simp only [traceSite, x, zero_add]
      omega
  have hzero : ix 0 = 0 := Fin.ext (by simp [ix])
  have hlast : ix n = Fin.last (d.1 + d.2) := Fin.ext (by simp [ix, hn])
  refine ⟨x, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i hi
    let j : Fin (d.1 + d.2) := ⟨i, by omega⟩
    have hjs : j.succ = ix (i + 1) := Fin.ext
      (by simp [j, ix, min_eq_left (show i + 1 ≤ n by omega)])
    have hjc : j.castSucc = ix i := Fin.ext (by simp [j, ix, min_eq_left hi.le])
    simpa only [hjs, hjc, x, Prod.fst_add, add_zero] using
      ((p.step j).imp (congrArg Prod.fst) (congrArg Prod.fst)).symm
  · intro i hi
    let j : Fin (d.1 + d.2) := ⟨i, by omega⟩
    have hjs : j.succ = ix (i + 1) := Fin.ext
      (by simp [j, ix, min_eq_left (show i + 1 ≤ n by omega)])
    rw [hx (i + 1) (by omega), ← hjs]
    exact hp j
  · simpa only [hx 0 (Nat.zero_le _), hzero, p.start] using hu
  · rw [hx n le_rfl, hlast, p.finish, hd]

/-- Open reachability propagates along a physical trace after contact. -/
theorem OpenTrace.extendReach {ω : Environment} {a : Lattice} {n m : ℕ}
    {x : ℕ → ℤ} (hx : OpenTrace ω a n x) {S : Set Lattice} {s t : ℕ}
    (hst : s ≤ t) (ht : t ≤ n)
    (hs : traceSite a s (x s) ∈ openReachSet (topSites ω) S (m + s)) :
    traceSite a t (x t) ∈ openReachSet (topSites ω) S (m + t) := by
  have hsum : s + (t - s) = t := Nat.add_sub_of_le hst
  have hseg := hx.segment s (t - s) (by omega)
  rw [hsum] at hseg
  have hin : ({traceSite a s (x s)} : Set Lattice) ⊆ openReachSet (topSites ω) S (m + s) :=
    singleton_subset_iff.mpr hs
  have h := openReachSet_mono (Set.Subset.refl (topSites ω)) hin (t - s) hseg
  rwa [openReachSet_add, Nat.add_assoc, hsum] at h

end LPPDifferentiability.FinalDraft.FlatBlockSource
