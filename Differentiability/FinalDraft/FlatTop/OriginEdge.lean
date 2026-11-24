/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatTop.OriginReach
import Differentiability.Model.OrientedPercolationLaws
import LPP_Foundations.Model.Paths.Nonempty

/-! The origin and half-line right edges agree whenever the origin reaches the level. -/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace LPPDifferentiability.FinalDraft

/-- The next reachable sites are the open north and east neighbours of the
currently reachable sites. -/
private theorem mem_openReachSet_succ_iff (O S : Set Lattice) (n : ℕ) (v : Lattice) :
    v ∈ openReachSet O S (n + 1) ↔
      v ∈ O ∧ (v - (1, 0) ∈ openReachSet O S n ∨
        v - (0, 1) ∈ openReachSet O S n) := by
  rw [← openReachSet_add]
  constructor
  · rintro ⟨u, hu, ⟨d, hd, q, hq⟩, hlevel⟩
    have hd₁ := congrArg Prod.fst hd
    have hd₂ := congrArg Prod.snd hd
    simp only [Prod.fst_add, Prod.snd_add, Nat.cast_one] at hd₁ hd₂ hlevel
    have hlen : d.1 + d.2 = 1 := by omega
    have hι : (⟨0, by omega⟩ : Fin (d.1 + d.2)).succ = Fin.last (d.1 + d.2) := by
      apply Fin.ext
      simp [hlen]
    have hV := hq ⟨0, by omega⟩
    rw [hι, q.finish, hd] at hV
    refine ⟨hV, ?_⟩
    by_cases he : d.1 = 1
    · left
      have hEq : v - (1, 0) = u := Prod.ext (by simp only [Prod.fst_sub]; omega)
        (by simp only [Prod.snd_sub]; omega)
      rwa [hEq]
    · right
      have hEq : v - (0, 1) = u := Prod.ext (by simp only [Prod.fst_sub]; omega)
        (by simp only [Prod.snd_sub]; omega)
      rwa [hEq]
  · rintro ⟨hv, hstep⟩
    have hneighbor (d : ℕ × ℕ) (hd : d.1 + d.2 = 1)
        (hu : v - ((d.1 : ℤ), (d.2 : ℤ)) ∈ openReachSet O S n) :
        v ∈ openReachSet O (openReachSet O S n) 1 := by
      let u := v - ((d.1 : ℤ), (d.2 : ℤ))
      have hfinish : u + ((d.1 : ℤ), (d.2 : ℤ)) = v := sub_add_cancel _ _
      obtain ⟨q⟩ := pathNonempty u d
      refine ⟨u, hu, ⟨d, hfinish, q, fun i => ?_⟩, ?_⟩
      · have hι : i.succ = Fin.last (d.1 + d.2) := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_last]
          have hi := i.isLt
          omega
        rw [hι, q.finish, hfinish]
        exact hv
      · have h₁ := congrArg Prod.fst hfinish
        have h₂ := congrArg Prod.snd hfinish
        simp only [Prod.fst_add, Prod.snd_add, Nat.cast_one] at h₁ h₂ ⊢
        omega
    rcases hstep with he | hn
    · exact hneighbor (1, 0) rfl he
    · exact hneighbor (0, 1) rfl hn

/-- At a fixed level, if a point reached from the half-line is at or to the
right of an origin-reached point, then the origin reaches it as well. -/
private theorem mem_origin_of_mem_halfLine_of_ge (O : Set Lattice) (n : ℕ)
    (u v : Lattice) (hu : u ∈ openReachSet O ({0} : Set Lattice) n)
    (hv : v ∈ openReachSet O antidiagHalfLine n) (huv : u.1 ≤ v.1) :
    v ∈ openReachSet O ({0} : Set Lattice) n := by
  have h₀ : ({0} : Set Lattice) ⊆ levelSet 0 := by
    rintro z hz
    rw [mem_singleton_iff.mp hz]
    simp [levelSet]
  have hH : antidiagHalfLine ⊆ levelSet 0 := fun _ hz => hz.1
  induction n generalizing u v with
  | zero =>
    rw [openReachSet_zero] at hu hv ⊢
    have hu0 := mem_singleton_iff.mp hu
    have hvx : v.1 ≤ 0 := hv.2
    have hvlev : v.1 + v.2 = 0 := hv.1
    rw [hu0] at huv
    have hv0 : v = 0 := Prod.ext (by simp only [Prod.fst_zero] at *; omega)
      (by simp only [Prod.fst_zero, Prod.snd_zero] at *; omega)
    exact mem_singleton_iff.mpr hv0
  | succ n ih =>
    have huLev : u.1 + u.2 = 0 + (n + 1 : ℤ) := by
      simpa only [Nat.cast_succ, levelSet, Set.mem_ofPred_eq] using openReachSet_subset_levelSet O _ 0 (n + 1) h₀ hu
    have hvLev : v.1 + v.2 = 0 + (n + 1 : ℤ) := by
      simpa only [Nat.cast_succ, levelSet, Set.mem_ofPred_eq] using openReachSet_subset_levelSet O _ 0 (n + 1) hH hv
    have hPred : ∃ u' ∈ openReachSet O ({0} : Set Lattice) n, u'.1 ≤ u.1 := by
      rcases ((mem_openReachSet_succ_iff O _ n u).mp hu).2 with he | hn
      · exact ⟨u - (1, 0), he, by simp only [Prod.fst_sub]; omega⟩
      · exact ⟨u - (0, 1), hn, by simp only [Prod.fst_sub]; omega⟩
    obtain ⟨u', hu', hu'x⟩ := hPred
    obtain ⟨hvO, hvPred⟩ := (mem_openReachSet_succ_iff O _ n v).mp hv
    apply (mem_openReachSet_succ_iff O _ n v).mpr
    refine ⟨hvO, ?_⟩
    rcases hvPred with hE | hN
    · by_cases hle : u'.1 ≤ (v - (1, 0) : Lattice).1
      · exact Or.inl (ih u' _ hu' hE hle)
      · have huv' : u.1 = v.1 := by
          simp only [Prod.fst_sub] at hle
          omega
        have heq : u = v := Prod.ext huv' (by omega)
        rw [← heq]
        exact ((mem_openReachSet_succ_iff O _ n u).mp hu).2
    · exact Or.inr (ih u' _ hu' hN (by simp only [Prod.fst_sub]; omega))

/-- The rightmost endpoints of the origin and half-line clusters agree at
every level the origin cluster reaches. -/
theorem openEdge_origin_eq_halfLine_of_nonempty
    (O : Set Lattice) (n : ℕ) (hn : (openReachSet O ({0} : Set Lattice) n).Nonempty) :
    openEdge O ({0} : Set Lattice) n = openEdge O antidiagHalfLine n := by
  let R := openReachSet O ({0} : Set Lattice) n
  let H := openReachSet O antidiagHalfLine n
  have hsub : R ⊆ H := openReachSet_mono subset_rfl
    (by rintro z hz; rw [mem_singleton_iff.mp hz]; simp [antidiagHalfLine]) n
  have hB : BddAbove (Prod.fst '' H) := by
    refine ⟨0 + n, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact bddAbove_fst_openReachSet O antidiagHalfLine n 0 (fun z hz => hz.2) v hv
  have hR : BddAbove (Prod.fst '' R) := hB.mono (image_mono hsub)
  obtain ⟨w, hw, hwx⟩ := maxFirst_mem R hn hR
  obtain ⟨v, hv, hvx⟩ := maxFirst_mem H (hn.mono hsub) hB
  have hle : w.1 ≤ v.1 := by
    rw [hvx]
    exact le_maxFirst H hB (hsub hw)
  have hvR : v ∈ R := mem_origin_of_mem_halfLine_of_ge O n w v hw hv hle
  change maxFirst R = maxFirst H
  rw [← hwx, ← hvx]
  have hvle := le_maxFirst R hR hvR
  rw [← hwx] at hvle
  exact le_antisymm hle hvle

/-- The almost-sure half-line limit is the limit of the actual origin
right edge on survival. -/
theorem isOriginRightEdgeSpeed_of_halfLine_limit (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (β : ℝ) (hlim : ∀ᵐ ω ∂environmentLaw ν,
      Tendsto (fun n : ℕ => (halfLineEdge ω n : ℝ) / (n : ℝ)) atTop (𝓝 β)) :
    IsOriginRightEdgeSpeed ν 1 β := by
  unfold IsOriginRightEdgeSpeed
  filter_upwards [hlim] with ω hω hsurv
  have hedge (n : ℕ) :
      openEdge {z | ω z = 1} ({0} : Set Lattice) n = halfLineEdge ω n :=
    openEdge_origin_eq_halfLine_of_nonempty _ n
      (openReachSet_origin_nonempty_of_survival hsurv n)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, hedge] using
    hω.comp (tendsto_add_atTop_nat 1)

end LPPDifferentiability.FinalDraft
