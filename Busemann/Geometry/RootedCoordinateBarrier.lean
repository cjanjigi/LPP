/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Geometry.GeodesicLowerCut
import LPP_Foundations.Model.LastPassage.Axes

@[expose] public section
open LPPDifferentiability
namespace LPP.Busemann

private theorem north_axis_locallyRightmost (ω : Environment) (u : Lattice) :
    IsLocallyRightmostGeodesic ω u (fun t : ℕ => u + ((0 : ℤ), (t : ℤ))) := by
  let north : ℕ → Lattice := fun t => u + ((0 : ℤ), (t : ℤ))
  have hnorthRoot : north 0 = u := by
    simp [north]
  have hnorthStep : ∀ t : ℕ,
      north (t + 1) = north t + ((0 : ℤ), (1 : ℤ)) := by
    intro t
    dsimp [north]
    apply Prod.ext
    · simp
    · simp only [Prod.snd_add]
      ring
  refine ⟨hnorthRoot, ?_, ?_⟩
  · intro t
    exact Or.inr (hnorthStep t)
  · intro m N _hN
    obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω (north m) (0, N)
    refine ⟨(0, N), p, by simp, ?_, hp, ?_⟩
    · intro i
      rw [Path.vertex_vertical p i]
      apply Prod.ext
      · simp [north]
      · simp [north, Nat.cast_add, add_assoc]
    · intro q _hq i
      rw [Path.vertex_vertical p i, Path.vertex_vertical q i]
      exact ⟨le_rfl, le_rfl⟩

/-- One deterministic rooted up-right path realizes every finite first-coordinate
cut, and its cut contains an actual locally rightmost geodesic. -/
theorem exists_rooted_coordinate_barrier
    (u : Lattice) (n k : ℕ) (hk : k ≤ n) :
    ∃ β : ℕ → Lattice,
      β 0 = u ∧
      (∀ t : ℕ,
        β (t + 1) = β t + ((1 : ℤ), (0 : ℤ)) ∨
          β (t + 1) = β t + ((0 : ℤ), (1 : ℤ))) ∧
      (∀ (ω : Environment) (γ : ℕ → Lattice),
        IsLocallyRightmostGeodesic ω u γ →
        (pathSoutheastLE γ β ↔ (γ n).1 ≤ u.1 + (k : ℤ))) ∧
      ∀ ω : Environment, ∃ γ : ℕ → Lattice,
        IsLocallyRightmostGeodesic ω u γ ∧ pathSoutheastLE γ β := by
  -- The east counts reach k by time n and then continue without bound.
  let eastCount : ℕ → ℕ := fun t => min t k + (t - n)
  let northCount : ℕ → ℕ := fun t => min (t - k) (n - k)
  let β : ℕ → Lattice := fun t =>
    u + ((eastCount t : ℤ), (northCount t : ℤ))

  have hβroot : β 0 = u := by
    simp [β, eastCount, northCount]

  -- The three time ranges give east, north, and east steps.
  have hβstep : ∀ t : ℕ,
      β (t + 1) = β t + ((1 : ℤ), (0 : ℤ)) ∨
        β (t + 1) = β t + ((0 : ℤ), (1 : ℤ)) := by
    intro t
    by_cases htk : t < k
    · left
      have htn : t < n := lt_of_lt_of_le htk hk
      have htn0 : t ≤ n := Nat.le_of_lt htn
      have htn1 : t + 1 ≤ n := by omega
      have htk0 : t ≤ k := by omega
      have htk1 : t + 1 ≤ k := by omega
      have hmin0 : min t k = t := Nat.min_eq_left htk0
      have hmin1 : min (t + 1) k = t + 1 := Nat.min_eq_left htk1
      have hsub0 : t - n = 0 := Nat.sub_eq_zero_of_le htn0
      have hsub1 : t + 1 - n = 0 := Nat.sub_eq_zero_of_le htn1
      have hnorth0 : min (t - k) (n - k) = 0 := by
        simp [Nat.sub_eq_zero_of_le (show t ≤ k by omega)]
      have hnorth1 : min (t + 1 - k) (n - k) = 0 := by
        simp [Nat.sub_eq_zero_of_le (show t + 1 ≤ k by omega)]
      apply Prod.ext
      · change u.1 + ((min (t + 1) k + (t + 1 - n) : ℕ) : ℤ) =
          (u.1 + ((min t k + (t - n) : ℕ) : ℤ)) + 1
        rw [hmin0, hmin1, hsub0, hsub1]
        simp only [Nat.cast_add, Nat.cast_one, add_zero]
        omega
      · change u.2 + ((min (t + 1 - k) (n - k) : ℕ) : ℤ) =
          (u.2 + ((min (t - k) (n - k) : ℕ) : ℤ)) + 0
        rw [hnorth0, hnorth1]
        simp only [Nat.cast_zero, add_zero]
    · by_cases htn : t < n
      · right
        have htk0 : k ≤ t := by omega
        have htk1 : k ≤ t + 1 := by omega
        have htn0 : t ≤ n := by omega
        have htn1 : t + 1 ≤ n := by omega
        have hmin0 : min t k = k := Nat.min_eq_right htk0
        have hmin1 : min (t + 1) k = k := Nat.min_eq_right htk1
        have hsub0 : t - n = 0 := Nat.sub_eq_zero_of_le htn0
        have hsub1 : t + 1 - n = 0 := Nat.sub_eq_zero_of_le htn1
        have hnorth0 : min (t - k) (n - k) = t - k :=
          Nat.min_eq_left (Nat.sub_le_sub_right htn0 k)
        have hnorth1 : min (t + 1 - k) (n - k) = t + 1 - k :=
          Nat.min_eq_left (Nat.sub_le_sub_right htn1 k)
        apply Prod.ext
        · change u.1 + ((min (t + 1) k + (t + 1 - n) : ℕ) : ℤ) =
            (u.1 + ((min t k + (t - n) : ℕ) : ℤ)) + 0
          rw [hmin0, hmin1, hsub0, hsub1]
          simp only [add_zero]
        · change u.2 + ((min (t + 1 - k) (n - k) : ℕ) : ℤ) =
            (u.2 + ((min (t - k) (n - k) : ℕ) : ℤ)) + 1
          rw [hnorth0, hnorth1]
          omega
      · left
        have hnt : n ≤ t := by omega
        have htk0 : k ≤ t := le_trans hk hnt
        have htk1 : k ≤ t + 1 := by omega
        have hmin0 : min t k = k := Nat.min_eq_right htk0
        have hmin1 : min (t + 1) k = k := Nat.min_eq_right htk1
        have hnorth0 : min (t - k) (n - k) = n - k :=
          Nat.min_eq_right (Nat.sub_le_sub_right hnt k)
        have hnorth1 : min (t + 1 - k) (n - k) = n - k :=
          Nat.min_eq_right (Nat.sub_le_sub_right (by omega : n ≤ t + 1) k)
        apply Prod.ext
        · change u.1 + ((min (t + 1) k + (t + 1 - n) : ℕ) : ℤ) =
            (u.1 + ((min t k + (t - n) : ℕ) : ℤ)) + 1
          rw [hmin0, hmin1]
          simp only [Nat.cast_add]
          omega
        · change u.2 + ((min (t + 1 - k) (n - k) : ℕ) : ℤ) =
            (u.2 + ((min (t - k) (n - k) : ℕ) : ℤ)) + 0
          rw [hnorth0, hnorth1]
          simp only [add_zero]

  -- The rooted unit steps fix the absolute level at every local time.
  have hβlevel : ∀ t : ℕ,
      (β t).1 + (β t).2 = u.1 + u.2 + (t : ℤ) := by
    intro t
    induction t with
    | zero => simp [hβroot]
    | succ t ih =>
        rcases hβstep t with heast | hnorth
        · rw [heast]
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
          omega
        · rw [hnorth]
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
          omega

  have hβfirst_before (t : ℕ) (htn : t ≤ n) :
      (β t).1 = u.1 + ((min t k : ℕ) : ℤ) := by
    change u.1 + ((min t k + (t - n) : ℕ) : ℤ) =
      u.1 + ((min t k : ℕ) : ℤ)
    rw [Nat.sub_eq_zero_of_le htn]
    simp only [add_zero]

  have hβfirst_after (t : ℕ) (hnt : n ≤ t) :
      (β t).1 = u.1 + (k : ℤ) + ((t - n : ℕ) : ℤ) := by
    change u.1 + ((min t k + (t - n) : ℕ) : ℤ) =
      u.1 + (k : ℤ) + ((t - n : ℕ) : ℤ)
    rw [Nat.min_eq_right (le_trans hk hnt)]
    simp only [Nat.cast_add]
    ring

  have hβfirst_at_n : (β n).1 = u.1 + (k : ℤ) := by
    rw [hβfirst_after n le_rfl]
    simp

  have hAxis : ∀ ω : Environment, ∃ γ : ℕ → Lattice,
      IsLocallyRightmostGeodesic ω u γ ∧ pathSoutheastLE γ β := by
    intro ω
    refine ⟨fun t => u + ((0 : ℤ), (t : ℤ)),
      north_axis_locallyRightmost ω u, ?_⟩
    have hγroot : (fun t : ℕ => u + ((0 : ℤ), (t : ℤ))) 0 = β 0 :=
      (north_axis_locallyRightmost ω u).1.trans hβroot.symm
    apply (pathSoutheastLE_iff_all_times_of_same_root
      (fun t : ℕ => u + ((0 : ℤ), (t : ℤ))) β hγroot).mpr
    intro t
    have hγlevel :
        ((fun s : ℕ => u + ((0 : ℤ), (s : ℤ))) t).1 +
          ((fun s : ℕ => u + ((0 : ℤ), (s : ℤ))) t).2 =
        u.1 + u.2 + (t : ℤ) := by
      simp only [Prod.fst_add, Prod.snd_add]
      ring
    have hbarrierLevel := hβlevel t
    have hbarrierFirst : u.1 ≤ (β t).1 := by
      change u.1 ≤ u.1 + (eastCount t : ℤ)
      exact le_add_of_nonneg_right (Int.natCast_nonneg (eastCount t))
    have hbarrierSecond : (β t).2 ≤ u.2 + (t : ℤ) := by omega
    change ((fun s : ℕ => u + ((0 : ℤ), (s : ℤ))) t).1 ≤ (β t).1 ∧
      (β t).2 ≤ ((fun s : ℕ => u + ((0 : ℤ), (s : ℤ))) t).2
    have haxisFirst :
        ((fun s : ℕ => u + ((0 : ℤ), (s : ℤ))) t).1 = u.1 := by simp
    have haxisSecond :
        ((fun s : ℕ => u + ((0 : ℤ), (s : ℤ))) t).2 = u.2 + (t : ℤ) := by simp
    rw [haxisFirst, haxisSecond]
    exact ⟨hbarrierFirst, hbarrierSecond⟩

  refine ⟨β, hβroot, hβstep, ?_, hAxis⟩
  intro ω γ hγ
  have hγstep := hγ.2.1
  have hγroot := hγ.1

  -- Each step changes the first coordinate by zero or one.
  have hγfirst_step (t : ℕ) :
      (γ t).1 ≤ (γ (t + 1)).1 ∧ (γ (t + 1)).1 ≤ (γ t).1 + 1 := by
    rcases hγstep t with heast | hnorth
    · rw [heast]
      simp only [Prod.fst_add]
      omega
    · rw [hnorth]
      simp only [Prod.fst_add]
      omega

  have hγfirst_mono : ∀ a b : ℕ, a ≤ b → (γ a).1 ≤ (γ b).1 := by
    intro a b hab
    induction b with
    | zero =>
        have ha : a = 0 := by omega
        subst a
        exact le_rfl
    | succ b ih =>
        by_cases hab' : a ≤ b
        · exact le_trans (ih hab') (hγfirst_step b).1
        · have ha : a = b + 1 := by omega
          subst a
          exact le_rfl

  have hγfirst_rise : ∀ a j : ℕ,
      (γ (a + j)).1 ≤ (γ a).1 + (j : ℤ) := by
    intro a j
    induction j with
    | zero => simp
    | succ j ih =>
        calc
          (γ (a + (j + 1))).1 = (γ (a + j + 1)).1 := by
            simp only [Nat.add_succ]
          _ ≤ (γ (a + j)).1 + 1 := by
            simpa only [Nat.add_succ] using (hγfirst_step (a + j)).2
          _ ≤ (γ a).1 + (j : ℤ) + 1 := by omega
          _ = (γ a).1 + ((j + 1 : ℕ) : ℤ) := by
            simp only [Nat.cast_succ]
            ring

  have hγfirst_by_time (t : ℕ) : (γ t).1 ≤ u.1 + (t : ℤ) := by
    simpa [hγroot] using hγfirst_rise 0 t

  have hγlevel : ∀ t : ℕ,
      (γ t).1 + (γ t).2 = u.1 + u.2 + (t : ℤ) := by
    intro t
    induction t with
    | zero => simp [hγroot]
    | succ t ih =>
        rcases hγstep t with heast | hnorth
        · rw [heast]
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
          omega
        · rw [hnorth]
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
          omega

  have hγfirst_below (hcut : (γ n).1 ≤ u.1 + (k : ℤ)) (t : ℕ) :
      (γ t).1 ≤ (β t).1 := by
    by_cases htn : t ≤ n
    · by_cases htk : t ≤ k
      · rw [hβfirst_before t htn, Nat.min_eq_left htk]
        exact hγfirst_by_time t
      · have hkt : k ≤ t := by omega
        rw [hβfirst_before t htn, Nat.min_eq_right hkt]
        exact le_trans (hγfirst_mono t n htn) hcut
    · have hnt : n ≤ t := by omega
      have hrise := hγfirst_rise n (t - n)
      have hindex : n + (t - n) = t := Nat.add_sub_of_le hnt
      rw [hindex] at hrise
      rw [hβfirst_after t hnt]
      have hcutRise : (γ n).1 + ((t - n : ℕ) : ℤ) ≤
          u.1 + (k : ℤ) + ((t - n : ℕ) : ℤ) := by omega
      exact le_trans hrise hcutRise

  have hγcoordinates_of_cut (hcut : (γ n).1 ≤ u.1 + (k : ℤ)) (t : ℕ) :
      (γ t).1 ≤ (β t).1 ∧ (β t).2 ≤ (γ t).2 := by
    have hfirst := hγfirst_below hcut t
    have hleft := hγlevel t
    have hright := hβlevel t
    exact ⟨hfirst, by omega⟩

  have hroot : γ 0 = β 0 := hγroot.trans hβroot.symm
  rw [pathSoutheastLE_iff_all_times_of_same_root γ β hroot]
  constructor
  · intro hbelow
    have hAtN := (hbelow n).1
    rw [hβfirst_at_n] at hAtN
    exact hAtN
  · intro hcut t
    exact hγcoordinates_of_cut hcut t

/-- The greatest geodesic in the same deterministic barrier cut has the
same finite first-coordinate threshold. -/
theorem exists_rooted_coordinate_barrier_greatest_cut
    (u : Lattice) (n k : ℕ) (hk : k ≤ n) :
    ∃ β : ℕ → Lattice,
      β 0 = u ∧
      (∀ t : ℕ,
        β (t + 1) = β t + ((1 : ℤ), (0 : ℤ)) ∨
          β (t + 1) = β t + ((0 : ℤ), (1 : ℤ))) ∧
      ∀ ω : Environment, ∃ q : ℕ → Lattice,
        IsLocallyRightmostGeodesic ω u q ∧ pathSoutheastLE q β ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
          ((γ n).1 ≤ u.1 + (k : ℤ) ↔ pathSoutheastLE γ q) := by
  obtain ⟨β, hβroot, hβstep, hcoordinate, hne⟩ :=
    exists_rooted_coordinate_barrier u n k hk
  refine ⟨β, hβroot, hβstep, ?_⟩
  intro ω
  obtain ⟨q, hq, hqbelow, hcut⟩ :=
    exists_greatest_geodesic_below_rooted_upRight_path
      ω u β hβroot hβstep (hne ω)
  refine ⟨q, hq, hqbelow, ?_⟩
  intro γ hγ
  have hcoordinate_cut := hcoordinate ω γ hγ
  constructor
  · intro hbound
    apply (hcut γ hγ).mp
    exact hcoordinate_cut.mpr hbound
  · intro hbelow
    apply hcoordinate_cut.mp
    exact (hcut γ hγ).mpr hbelow

end LPP.Busemann
