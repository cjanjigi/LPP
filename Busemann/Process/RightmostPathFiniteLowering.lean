/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RightmostPathCalibratedCrossing
public import Busemann.Process.RightmostPathShielding
public import Busemann.Process.RightmostPathOutsideAgreement
public import Busemann.Process.RightmostPathCorridor
public import LPP_Foundations.Model.Paths.BoundaryDetour
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! Deterministic finite lowering excludes west or south approach to the middle tail. -/

@[expose] public section
open LPPDifferentiability
open scoped BigOperators

namespace LPP.Busemann

-- Split the west boundary below ell and reindex the whole terminal-excluded interval.
private theorem west_tail_strict_after_entry
    (ω : Environment) (K : ℝ) (ell : ℕ) (M2 j : ℤ)
    (hj : 0 < j) (hjell : j < (ell : ℤ)) (hTop : (ell : ℤ) < M2)
    (hPrefix : ∀ t : ℤ, 0 ≤ t → t < (ell : ℤ) → K ≤ ω (0, t))
    (hTail : ((M2 - (ell : ℤ) : ℤ) : ℝ) * K <
      ∑ t ∈ Finset.Ico (ell : ℤ) M2, ω (0, t)) :
    (((M2 - j).toNat - 1 : ℕ) : ℝ) * K <
      ∑ r : Fin ((M2 - j).toNat - 1),
        ω ((0, j) + ((0 : ℤ), ((r.val + 1 : ℕ) : ℤ))) := by
  have hleft : j + 1 ≤ (ell : ℤ) := by omega
  have hright : (ell : ℤ) ≤ M2 := by omega
  have hsumLower : (∑ _t ∈ Finset.Ico (j + 1) (ell : ℤ), K) ≤
      ∑ t ∈ Finset.Ico (j + 1) (ell : ℤ), ω (0, t) := by
    apply Finset.sum_le_sum
    intro t ht
    have ht' := Finset.mem_Ico.mp ht
    exact hPrefix t (by omega) ht'.2
  have hcardZ : ((Finset.Ico (j + 1) (ell : ℤ)).card : ℤ) =
      (ell : ℤ) - (j + 1) := Int.card_Ico_of_le (j + 1) (ell : ℤ) hleft
  have hcardR : ((Finset.Ico (j + 1) (ell : ℤ)).card : ℝ) =
      ((ell : ℤ) - (j + 1) : ℤ) := by exact_mod_cast hcardZ
  simp only [Finset.sum_const, nsmul_eq_mul, hcardR] at hsumLower
  have hsplit : (∑ t ∈ Finset.Ico (j + 1) M2, ω (0, t)) =
      (∑ t ∈ Finset.Ico (j + 1) (ell : ℤ), ω (0, t)) +
        ∑ t ∈ Finset.Ico (ell : ℤ) M2, ω (0, t) := by
    rw [← Finset.Ico_union_Ico_eq_Ico hleft hright,
      Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _)]
  have hdiff : 0 ≤ M2 - j := by omega
  have hcast : ((M2 - j).toNat : ℤ) = M2 - j := Int.toNat_of_nonneg hdiff
  have hlen : (M2 - (j + 1)).toNat = (M2 - j).toNat - 1 := by
    have hc : ((M2 - (j + 1)).toNat : ℤ) = M2 - (j + 1) :=
      Int.toNat_of_nonneg (by omega)
    omega
  have hlenR : (((M2 - j).toNat - 1 : ℕ) : ℝ) =
      ((M2 - j - 1 : ℤ) : ℝ) := by
    have hc : (((M2 - j).toNat - 1 : ℕ) : ℤ) = M2 - j - 1 := by omega
    exact_mod_cast hc
  have hstrict : (((M2 - j).toNat - 1 : ℕ) : ℝ) * K <
      ∑ t ∈ Finset.Ico (j + 1) M2, ω (0, t) := by
    rw [hlenR, hsplit]
    push_cast at hsumLower hTail ⊢
    linarith
  have hreindex : (∑ t ∈ Finset.Ico (j + 1) M2, ω (0, t)) =
      ∑ r : Fin ((M2 - j).toNat - 1),
        ω ((0, j) + ((0 : ℤ), ((r.val + 1 : ℕ) : ℤ))) := by
    rw [Int.Ico_eq_finset_map, Finset.sum_map, hlen, Finset.sum_range]
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    apply Prod.ext
    · simp
    · simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
        addLeftEmbedding_apply, Prod.snd_add, Nat.cast_add, Nat.cast_one]
      omega
  rwa [hreindex] at hstrict

/-- A finite lowering of the high-weight corridor prevents a path from west
or south from meeting the preserved middle tail. This is the deterministic
finite detour argument in GRS arXiv:1510.00860v1, Appendix A.4 and A.5,
lines 1588–1632 and 1690–1777. -/
theorem rightmost_middle_tail_avoids_west_or_south_of_finite_lowering
    (ω ω' : Environment) (C D : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hD : is_additive D)
    (hRecC : recovers_environment ω C)
    (hRecD : recovers_environment ω' D)
    (m ell : ℕ) (hm : 0 < m) (hmell : m < ell)
    (M1 M2 a1 a2 H : ℤ) (hTop : (ell : ℤ) < M2)
    (nL nM nU nE : ℕ)
    (hNorthL : rightmostCocyclePath C 0 nL = (M1, M2))
    (hNorthM : rightmostCocyclePath C (0, (m : ℤ)) nM = (a2, M2))
    (hNorthU : rightmostCocyclePath C (0, (ell : ℤ)) nU = (a1, M2))
    (hEastU : rightmostCocyclePath C (0, (ell : ℤ)) nE = (M1, H))
    (hDisjointLM : ∀ r s : ℕ,
      rightmostCocyclePath C 0 r ≠
        rightmostCocyclePath C (0, (m : ℤ)) s)
    (hDisjointMU : ∀ r s : ℕ,
      rightmostCocyclePath C (0, (m : ℤ)) r ≠
        rightmostCocyclePath C (0, (ell : ℤ)) s)
    (R : Finset Lattice)
    (hR : ∀ z : Lattice, z ∈ R ↔
      0 < z.1 ∧ z.2 < M2 ∧
      ∃ n : ℕ, (n : ℤ) = z.1 + z.2 ∧
        (rightmostCocyclePath C 0 n).2 < z.2 ∧
        (n < ell ∨ z.2 <
          (rightmostCocyclePath C (0, (ell : ℤ)) (n - ell)).2))
    (V : Finset Lattice) (K : ℝ)
    (hV : ∀ z : Lattice, z ∈ V ↔ z ∈ R ∧ K < ω z)
    (hSmallOnV : ∀ z ∈ V, ω' z ≤ K)
    (hOutsideWeights : ∀ z : Lattice, z ∉ V → ω' z = ω z)
    (hOutsideEdges : ∀ y : Lattice, y ∈ outsideLowerOrthants V →
      ∀ e : Fin 2,
        D y (y + finiteEdgeStep e) = C y (y + finiteEdgeStep e))
    (hWestPrefix : ∀ j : ℤ, 0 ≤ j → j < (ell : ℤ) → K ≤ ω (0, j))
    (hWestTail : ((M2 - (ell : ℤ) : ℤ) : ℝ) * K <
      ∑ j ∈ Finset.Ico (ell : ℤ) M2, ω (0, j))
    (hNorthWeights : ∀ i : ℤ, 0 ≤ i → i ≤ M1 → K ≤ ω (i, M2)) :
    ∀ v : Lattice, v ∉ Set.Icc (0 : Lattice) (M1, M2) →
      (v.1 ≤ 0 ∨ v.2 ≤ 0) → ∀ N k : ℕ,
        rightmostCocyclePath D v N ≠
          rightmostCocyclePath D (a2, M2) k := by
  classical
  -- The unique set described by the input is the constructed finite corridor.
  obtain ⟨R0, hR0, hR0Box, hR0Avoid⟩ :=
    exists_finite_rightmost_path_corridor C ell M1 M2 nL hNorthL
  have hEqR : R = R0 := by
    ext z
    rw [hR z, hR0 z]
  have hRbox : ∀ z ∈ R, 0 < z.1 ∧ z.1 < M1 ∧ 0 < z.2 ∧ z.2 < M2 := by
    intro z hz
    apply hR0Box z
    simpa only [hEqR] using hz
  have hRavoid : ∀ n, rightmostCocyclePath C 0 n ∉ R ∧
      rightmostCocyclePath C (0, (ell : ℤ)) n ∉ R := by
    simpa only [hEqR] using hR0Avoid
  have hVsub : ∀ z ∈ V, z ∈ R := fun z hz => ((hV z).mp hz).1
  have hVbox : ∀ z ∈ V, z.1 < M1 ∧ z.2 < M2 := by
    intro z hz
    have h := hRbox z (hVsub z hz)
    exact ⟨h.2.1, h.2.2.2⟩
  have hVavoid : ∀ n, rightmostCocyclePath C 0 n ∉ V ∧
      rightmostCocyclePath C (0, (ell : ℤ)) n ∉ V := by
    intro n
    exact ⟨fun h => (hRavoid n).1 (hVsub _ h),
      fun h => (hRavoid n).2 (hVsub _ h)⟩
  -- The exact high-site modification lowers all weights and bounds the corridor.
  have hLower : ∀ z, ω' z ≤ ω z := by
    intro z
    by_cases hz : z ∈ V
    · exact le_trans (hSmallOnV z hz) (le_of_lt ((hV z).mp hz).2)
    · exact le_of_eq (hOutsideWeights z hz)
  have hSmallR : ∀ z ∈ R, ω' z ≤ K := by
    intro z hz
    by_cases hv : z ∈ V
    · exact hSmallOnV z hv
    · rw [hOutsideWeights z hv]
      by_contra! hhigh
      exact hv ((hV z).mpr ⟨hz, hhigh⟩)
  have hWestEq (t : ℤ) : ω' (0, t) = ω (0, t) := by
    apply hOutsideWeights
    intro hv
    have hr := hRbox (0, t) (hVsub _ hv)
    simp only at hr
    omega
  have hNorthEq (t : ℤ) : ω' (t, M2) = ω (t, M2) := by
    apply hOutsideWeights
    intro hv
    have hr := hRbox (t, M2) (hVsub _ hv)
    simp only at hr
    omega
  -- The two barriers and preserved tail come from the existing producers.
  have hbarriers := rightmost_paths_outer_shielding ω ω' C D hC hD hRecC hRecD
    hLower V (ell : ℤ) M1 M2 H nL nE hVbox hOutsideWeights hVavoid
    hNorthL hEastU hOutsideEdges
  have hUpperEdges : ∀ y : Lattice, (a2, M2) ≤ y → ∀ e : Fin 2,
      D y (y + finiteEdgeStep e) = C y (y + finiteEdgeStep e) := by
    intro y hy e
    apply hOutsideEdges y ?_ e
    change ∀ z ∈ V, ¬ y ≤ z
    intro z hz hyz
    have hz2 := (hVbox z hz).2
    have hy2 := (Prod.le_def.mp hy).2
    have hyz2 := (Prod.le_def.mp hyz).2
    simp only at hy2
    omega
  have hTail : ∀ r, rightmostCocyclePath D (a2, M2) r =
      rightmostCocyclePath C (a2, M2) r :=
    rightmostCocyclePath_eq_of_upper_orthant_edge_eq C D (a2, M2) (a2, M2)
      le_rfl hUpperEdges
  intro v hv hWestSouth N k hMeet
  obtain ⟨entry, exit, j, i, hEntryPos, hEntryExit, hExitN, hJPos, hJell,
      ha1i, hiM1, hiPos, hEntry, hNext, hExit, hAfterX, hBeforeY, hInside,
      p, hpTrace, hpCal, hpInside, hpPotential, hpMaximum⟩ :=
    exists_calibrated_rightmost_corridor_crossing ω' C D hD hRecD
      m ell hm hmell M1 M2 a1 a2 hTop nL nM nU hNorthL hNorthM hNorthU
      hDisjointLM hDisjointMU hTail hbarriers.1 hbarriers.2 R hR
      v hv hWestSouth N k hMeet
  have haCast : ((M2 - j).toNat : ℤ) = M2 - j := Int.toNat_of_nonneg (by omega)
  have hbCast : (i.toNat : ℤ) = i := Int.toNat_of_nonneg (by omega)
  have ha : 0 < (M2 - j).toNat := by omega
  have hb : 0 < i.toNat := by omega
  have hInterior : ∀ r : Fin (i.toNat + (M2 - j).toNat), 0 < r.val →
      ω' (p.vertex r.castSucc) ≤ K := by
    intro r hr
    exact hSmallR _ (hpInside r hr)
  have hWestOld := west_tail_strict_after_entry ω K ell M2 j
    hJPos hJell hTop hWestPrefix hWestTail
  have hWest : (((M2 - j).toNat - 1 : ℕ) : ℝ) * K <
      ∑ r : Fin ((M2 - j).toNat - 1),
        ω' ((0, j) + ((0 : ℤ), ((r.val + 1 : ℕ) : ℤ))) := by
    convert hWestOld using 1
    apply Finset.sum_congr rfl
    intro r _
    have hp : (0, j) + ((0 : ℤ), ((r.val + 1 : ℕ) : ℤ)) =
        (0, j + ((r.val + 1 : ℕ) : ℤ)) := by
      apply Prod.ext <;> simp
    rw [hp, hWestEq]
  have hNorth : ∀ r : Fin i.toNat, K ≤
      ω' ((0, j) + (Int.ofNat r.val, Int.ofNat (M2 - j).toNat)) := by
    intro r
    have hr : (r.val : ℤ) ≤ M1 := by have h := r.isLt; omega
    have hw := hNorthWeights (r.val : ℤ) (by omega) hr
    have hp : (0, j) + (Int.ofNat r.val, Int.ofNat (M2 - j).toNat) =
        ((r.val : ℤ), M2) := by
      apply Prod.ext
      · change (0 : ℤ) + (r.val : ℤ) = (r.val : ℤ)
        simp
      · change j + ((M2 - j).toNat : ℤ) = M2
        omega
    rw [hp, hNorthEq]
    exact hw
  obtain ⟨q, _, _, hStrict⟩ :=
    exists_vertical_then_horizontal_strict_detour ω' (0, j)
      (M2 - j).toNat i.toNat ha hb K p hInterior hWest hNorth
  have hUpper := pathWeight_le_lastPassage ω' q
  rw [← hpMaximum] at hUpper
  exact (not_lt_of_ge hUpper) hStrict

end LPP.Busemann
