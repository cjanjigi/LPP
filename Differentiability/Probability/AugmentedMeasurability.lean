/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.OrientedPercolation
public import Differentiability.Probability.LevelSigma
import Differentiability.Model.AugmentedPassage
import Differentiability.Model.OrientedPercolationLaws
import LPP_Foundations.Model.Paths.Level
import Mathlib.Tactic.Ring

/-!
# Measurability of the augmented process

For each block index
`j`, the occupied set `X_j` of the augmented process, the count `K_j`, the lowest point of
`X_j` and the triangle event at that lowest point are measurable with respect to the
weights at levels at most `j T` (at most `j T + T` for the triangle event).

The differentiability preprint, Section 2.3, does not state these facts. They are the
measurability steps that the freezing argument for the augmentation step needs: they say that
the random block `j`, and the decision to augment there, are determined by the weights below
level `j T`, so that the later weights can be treated as independent of them.

The proof has three layers.
* Single weights and countable events. Every event "a given weight equals `1`" or "lies in
  a given measurable set of reals" is measurable for the levels that contain that site.
  Open reach events are countable unions over paths of finite intersections of such events.
* Random sets of sites. If membership of each site in a random set is measurable, then the
  largest first coordinate of the set is measurable, with the junk value `0` for sets that
  are empty or unbounded above.
* The process. One step of `augmentedProcess` keeps the open reach of the current set, and
  adds the triangle targets at the lowest point when a guard holds. Splitting the guard
  according to the (integer) value of the lowest point turns it into a countable union of
  events at fixed sites. This gives an induction on `j`.

All proofs treat `augmentedProcess` through two one-step lemmas, proved by `rw` at the
successor index.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

@[expose] public section

namespace LPPDifferentiability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

/-! ## Single weights -/

/-- A single weight at a site of level at most `m` is measurable for the weights at levels at
most `m`. -/
private theorem measurable_site (m : ℤ) {z : Lattice} (hz : z.1 + z.2 ≤ m) :
    Measurable[levelsAtMost m] (fun ω : Environment => ω z) := by
  have hle : MeasurableSpace.comap (fun ω : Environment => ω z)
      (inferInstance : MeasurableSpace ℝ) ≤ levelsAtMost m :=
    le_iSup₂ (f := fun (z : Lattice) (_ : z.1 + z.2 ≤ m) =>
      MeasurableSpace.comap (fun ω : Environment => ω z)
        (inferInstance : MeasurableSpace ℝ)) z hz
  exact Measurable.mono (comap_measurable (fun ω : Environment => ω z)) hle le_rfl

/-- The event that a weight lies in a measurable set of reals, for a site of level at most
`m`, is measurable for the weights at levels at most `m`. -/
private theorem measurableSet_site_mem (m : ℤ) {z : Lattice} (hz : z.1 + z.2 ≤ m)
    {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet[levelsAtMost m] {ω : Environment | ω z ∈ B} :=
  measurable_site m hz hB

/-- The event that a weight equals `1`, for a site of level at most `m`. -/
theorem measurableSet_site_one (m : ℤ) {z : Lattice} (hz : z.1 + z.2 ≤ m) :
    MeasurableSet[levelsAtMost m] {ω : Environment | ω z = 1} :=
  measurable_site m hz (measurableSet_singleton (1 : ℝ))

/-! ## Comparison of the level sigma-algebras -/

/-- The sigma-algebra of the weights at levels at most `m` lies inside the product
sigma-algebra on environments. This formalizes the remark that information at levels at most
`m` is ordinary information about the environment. -/
theorem levelsAtMost_le (m : ℤ) :
    levelsAtMost m ≤ (inferInstance : MeasurableSpace Environment) :=
  iSup₂_le fun _ _ => (measurable_pi_apply _).comap_le

/-- More levels carry more information: the sigma-algebras `levelsAtMost m` increase with
`m`. -/
theorem levelsAtMost_mono {m m' : ℤ} (h : m ≤ m') : levelsAtMost m ≤ levelsAtMost m' :=
  iSup₂_le fun z hz =>
    le_iSup₂ (f := fun (z : Lattice) (_ : z.1 + z.2 ≤ m') =>
      MeasurableSpace.comap (fun ω : Environment => ω z)
        (inferInstance : MeasurableSpace ℝ)) z (hz.trans h)

/-- A set that is measurable for the levels at most `m` is measurable for the levels at most
`m'`, when `m ≤ m'`. -/
private theorem measurableSet_levels_mono {m m' : ℤ} (h : m ≤ m') {s : Set Environment}
    (hs : MeasurableSet[levelsAtMost m] s) : MeasurableSet[levelsAtMost m'] s :=
  levelsAtMost_mono h _ hs

/-! ## The lowest point of a random set -/

/-- When `R` is nonempty and bounded above in the first coordinate, `j ≤ maxFirst R` means
that some site of `R` has first coordinate at least `j`. Otherwise `maxFirst R` is `0`. -/
theorem le_maxFirst_iff (R : Set Lattice) (j : ℤ) :
    j ≤ maxFirst R ↔ ((R.Nonempty ∧ BddAbove (Prod.fst '' R)) ∧ ∃ v ∈ R, j ≤ v.1) ∨
      (j ≤ 0 ∧ ¬ (R.Nonempty ∧ BddAbove (Prod.fst '' R))) := by
  by_cases h : R.Nonempty ∧ BddAbove (Prod.fst '' R)
  · obtain ⟨w, hw, hwm⟩ := maxFirst_mem R h.1 h.2
    refine ⟨fun hj => Or.inl ⟨h, w, hw, by omega⟩, ?_⟩
    rintro (⟨-, v, hv, hjv⟩ | ⟨-, hn⟩)
    · exact hjv.trans (le_maxFirst R h.2 hv)
    · exact absurd h hn
  · have h0 : maxFirst R = 0 := by
      unfold maxFirst
      by_cases hb : BddAbove (Prod.fst '' R)
      · have hR : R = ∅ := by
          by_contra hR
          exact h ⟨Set.nonempty_iff_ne_empty.2 hR, hb⟩
        rw [hR, Set.image_empty]
        exact Int.csSup_empty
      · exact Int.csSup_of_not_bddAbove hb
    rw [h0]
    exact ⟨fun hj => Or.inr ⟨hj, h⟩, fun hh => hh.elim (fun hh => absurd hh.1 h) fun hh => hh.1⟩

/-- A set of sites is nonempty exactly when some site has first coordinate at least some
integer. -/
theorem nonempty_iff_exists (R : Set Lattice) :
    R.Nonempty ↔ ∃ j : ℤ, ∃ v ∈ R, j ≤ v.1 :=
  ⟨fun ⟨v, hv⟩ => ⟨v.1, v, hv, le_rfl⟩, fun ⟨_, v, hv, _⟩ => ⟨v, hv⟩⟩

/-- First coordinates are bounded above exactly when, for some bound `b`, no site has first
coordinate at least `b + 1`. -/
theorem bddAbove_iff_exists (R : Set Lattice) :
    BddAbove (Prod.fst '' R) ↔ ∃ b : ℤ, ¬ ∃ v ∈ R, b + 1 ≤ v.1 := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, fun ⟨v, hv, h⟩ => by have := hb ⟨v, hv, rfl⟩; omega⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    by_contra h
    exact hb ⟨v, hv, by omega⟩

/-- The largest first coordinate of a random set of sites is measurable as soon as the
membership of every fixed site is measurable. No boundedness is needed: the value `0` that
`maxFirst` takes for empty or unbounded sets is also a measurable case. This is the
measurability of the lowest point used in the augmentation step. -/
theorem measurable_maxFirst_of_measurableSet_mem {Ω : Type*} (mΩ : MeasurableSpace Ω)
    (X : Ω → Set Lattice) (hX : ∀ z : Lattice, MeasurableSet[mΩ] {ω | z ∈ X ω}) :
    Measurable[mΩ] fun ω => maxFirst (X ω) := by
  -- "Some site of `X ω` has first coordinate at least `i`" is a countable union.
  have hP : ∀ i : ℤ, MeasurableSet[mΩ] {ω | ∃ v ∈ X ω, i ≤ v.1} := by
    intro i
    have hEq : {ω : Ω | ∃ v ∈ X ω, i ≤ v.1} =
        ⋃ v : Lattice, {ω : Ω | v ∈ X ω} ∩ {_ω : Ω | i ≤ v.1} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    rw [hEq]
    exact MeasurableSet.iUnion fun v => (hX v).inter (MeasurableSet.const _)
  refine measurable_of_Ici fun j => ?_
  have hN : MeasurableSet[mΩ] (⋃ i : ℤ, {ω : Ω | ∃ v ∈ X ω, i ≤ v.1}) :=
    MeasurableSet.iUnion fun i => hP i
  have hB : MeasurableSet[mΩ] (⋃ b : ℤ, ({ω : Ω | ∃ v ∈ X ω, b + 1 ≤ v.1})ᶜ) :=
    MeasurableSet.iUnion fun b => (hP _).compl
  -- The event `j ≤ maxFirst (X ω)`: either a genuine maximum at least `j`, or the junk
  -- value `0` with `j ≤ 0`.
  have hEq : (fun ω : Ω => maxFirst (X ω)) ⁻¹' Ici j =
      ((⋃ i : ℤ, {ω : Ω | ∃ v ∈ X ω, i ≤ v.1}) ∩
        (⋃ b : ℤ, ({ω : Ω | ∃ v ∈ X ω, b + 1 ≤ v.1})ᶜ) ∩ {ω : Ω | ∃ v ∈ X ω, j ≤ v.1}) ∪
      ({_ω : Ω | j ≤ 0} ∩ ((⋃ i : ℤ, {ω : Ω | ∃ v ∈ X ω, i ≤ v.1}) ∩
        (⋃ b : ℤ, ({ω : Ω | ∃ v ∈ X ω, b + 1 ≤ v.1})ᶜ))ᶜ) := by
    ext ω
    simp only [mem_preimage, mem_Ici, le_maxFirst_iff, mem_union, mem_inter_iff, mem_iUnion,
      mem_compl_iff, mem_ofPred_eq, nonempty_iff_exists, bddAbove_iff_exists]
  rw [hEq]
  exact ((hN.inter hB).inter (hP j)).union
    ((MeasurableSet.const (j ≤ 0)).inter (hN.inter hB).compl)

/-! ## Open reach from a random set on a fixed level -/

/-- The set of paths with a given start and step counts is countable (a path is determined
by its vertices). -/
theorem countable_path (u : Lattice) (d : ℕ × ℕ) : Countable (Path u d) := by
  refine Function.Injective.countable (f := Path.vertex) ?_
  rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h
  cases h
  rfl

/-- For `u` on level `m` and `v` on level `m + n`, the event that an open path leads from
`u` to `v` reads only weights at levels `m + 1` to `m + n`. -/
theorem measurableSet_openReach (m : ℤ) (n : ℕ) (u v : Lattice)
    (hu : u.1 + u.2 = m) (hv : v.1 + v.2 = m + n) :
    MeasurableSet[levelsAtMost (m + n)] {ω : Environment | OpenReach (topSites ω) u v} := by
  have hEq : {ω : Environment | OpenReach (topSites ω) u v} =
      ⋃ d : ℕ × ℕ, ⋃ (_ : u + ((d.1 : ℤ), (d.2 : ℤ)) = v), ⋃ p : Path u d,
        ⋂ i : Fin (d.1 + d.2), {ω : Environment | ω (p.vertex i.succ) = 1} := by
    ext ω
    simp only [OpenReach, mem_ofPred_eq, mem_iUnion, mem_iInter, exists_prop]
    rfl
  rw [hEq]
  refine MeasurableSet.iUnion fun d => MeasurableSet.iUnion fun hd => ?_
  have := countable_path u d
  refine MeasurableSet.iUnion fun p => MeasurableSet.iInter fun i => ?_
  have h1 := congrArg Prod.fst hd
  have h2 := congrArg Prod.snd hd
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  have hl := p.level i.succ
  have hi := i.isLt
  rw [Fin.val_succ] at hl
  push_cast at hl
  exact measurableSet_site_one _ (by omega)

/-- Membership in the set reached in `n` open steps from a random start set on level `L` is
measurable for the weights at levels at most `L + n`, when membership in the start set is
measurable for the levels at most `L`. The event is the countable union over start sites
`u` of "`u` is in the start set and an open path leads from `u` to `v`"
(the first step of the augmentation induction). -/
theorem measurableSet_mem_openReachSet_levelsAtMost (L : ℤ) (n : ℕ)
    (X : Environment → Set Lattice) (hXlev : ∀ ω, X ω ⊆ levelSet L)
    (hX : ∀ z : Lattice, MeasurableSet[levelsAtMost L] {ω | z ∈ X ω}) (v : Lattice) :
    MeasurableSet[levelsAtMost (L + n)] {ω | v ∈ openReachSet (topSites ω) (X ω) n} := by
  have hle : (L : ℤ) ≤ L + n := by omega
  have hEq : {ω : Environment | v ∈ openReachSet (topSites ω) (X ω) n} =
      ⋃ u : Lattice, ⋃ (_ : u.1 + u.2 = L), ⋃ (_ : v.1 + v.2 = L + n),
        ({ω : Environment | u ∈ X ω} ∩ {ω : Environment | OpenReach (topSites ω) u v}) := by
    ext ω
    simp only [openReachSet, mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · rintro ⟨u, hu, hr, hl⟩
      have h : u.1 + u.2 = L := hXlev ω hu
      exact ⟨u, h, by omega, hu, hr⟩
    · rintro ⟨u, h, hv, hu, hr⟩
      exact ⟨u, hu, hr, by omega⟩
  rw [hEq]
  refine MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun hu =>
    MeasurableSet.iUnion fun hv => ?_
  exact (measurableSet_levels_mono hle (hX u)).inter (measurableSet_openReach L n u v hu hv)

/-! ## The triangle event at a fixed site -/

/-- The triangle event at a fixed site `r` reads only the weights at levels `r₁ + r₂ + 1`
to `r₁ + r₂ + T`, hence is measurable for the levels at most `r₁ + r₂ + T`. The hypothesis
`1 ≤ T` is needed: for `T = 0` the condition still reads the right neighbour of `r`, which
lies one level up. -/
theorem measurableSet_isTriangle_levelsAtMost (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ) (r : Lattice) :
    MeasurableSet[levelsAtMost (r.1 + r.2 + T)] {ω : Environment | IsTriangle ω T c₀ r} := by
  -- The three clauses of `IsTriangle`, each as a countable intersection of site events.
  have hEq : {ω : Environment | IsTriangle ω T c₀ r} =
      (⋂ i : ℕ, ⋂ (_ : 1 ≤ i), ⋂ (_ : i ≤ T),
        {ω : Environment | ω (r.1, r.2 + i) ∈ Iio (1 : ℝ)}) ∩
      (({ω : Environment | ω (r.1 + 1, r.2) ∈ Ici c₀} ∩
          {ω : Environment | ω (r.1 + 1, r.2) ∈ Iio (1 : ℝ)}) ∩
        ⋂ z : Lattice, ⋂ (_ : r.1 + 1 ≤ z.1), ⋂ (_ : r.2 ≤ z.2),
          ⋂ (_ : (z.1 - (r.1 + 1)) + (z.2 - r.2) ≤ (T : ℤ) - 1),
            ⋂ (_ : z ≠ (r.1 + 1, r.2)), {ω : Environment | ω z = 1}) := by
    ext ω
    simp only [IsTriangle, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_Ici, mem_Iio]
  have hA : MeasurableSet[levelsAtMost (r.1 + r.2 + T)]
      (⋂ i : ℕ, ⋂ (_ : 1 ≤ i), ⋂ (_ : i ≤ T),
        {ω : Environment | ω (r.1, r.2 + i) ∈ Iio (1 : ℝ)}) := by
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun h1 =>
      MeasurableSet.iInter fun h2 => ?_
    exact measurableSet_site_mem _
      (by show r.1 + (r.2 + (i : ℤ)) ≤ r.1 + r.2 + (T : ℤ); omega) measurableSet_Iio
  have hz1 : ((r.1 + 1, r.2) : Lattice).1 + ((r.1 + 1, r.2) : Lattice).2 ≤ r.1 + r.2 + T := by
    show r.1 + 1 + r.2 ≤ r.1 + r.2 + (T : ℤ)
    omega
  have hB : MeasurableSet[levelsAtMost (r.1 + r.2 + T)]
      ({ω : Environment | ω (r.1 + 1, r.2) ∈ Ici c₀} ∩
        {ω : Environment | ω (r.1 + 1, r.2) ∈ Iio (1 : ℝ)}) :=
    (measurableSet_site_mem _ hz1 measurableSet_Ici).inter
      (measurableSet_site_mem _ hz1 measurableSet_Iio)
  have hC : MeasurableSet[levelsAtMost (r.1 + r.2 + T)]
      (⋂ z : Lattice, ⋂ (_ : r.1 + 1 ≤ z.1), ⋂ (_ : r.2 ≤ z.2),
        ⋂ (_ : (z.1 - (r.1 + 1)) + (z.2 - r.2) ≤ (T : ℤ) - 1),
          ⋂ (_ : z ≠ (r.1 + 1, r.2)), {ω : Environment | ω z = 1}) := by
    refine MeasurableSet.iInter fun z => MeasurableSet.iInter fun h1 =>
      MeasurableSet.iInter fun h2 => MeasurableSet.iInter fun h3 =>
        MeasurableSet.iInter fun _ => ?_
    exact measurableSet_site_one _ (by omega)
  rw [hEq]
  exact hA.inter (hB.inter hC)

/-! ## One step of the augmented process -/

/-- The lowest point `(maxFirst X, j T - maxFirst X)` of a set `X` on level `j T`. -/
private noncomputable abbrev lowPt (T j : ℕ) (X : Set Lattice) : Lattice :=
  (maxFirst X, (j : ℤ) * T - maxFirst X)

/-- The guard of the augmentation step at block `j`: fewer than `k` augmentations so far, the
lowest point lies in the current set `X`, and there is a triangle at the lowest point. -/
private abbrev guardAt (ω : Environment) (T : ℕ) (c₀ : ℝ) (k j : ℕ) (X : Set Lattice)
    (K : ℕ) : Prop :=
  K < k ∧ lowPt T j X ∈ X ∧ IsTriangle ω T c₀ (lowPt T j X)

/-- When the guard holds, the next pair is the open reach joined with the triangle targets,
with the count raised by one. -/
private theorem augmentedProcess_succ_of (ω : Environment) (T : ℕ) (c₀ : ℝ)
    (S : Set Lattice) (k j : ℕ)
    (h : guardAt ω T c₀ k j (augmentedProcess ω T c₀ S k j).1
      (augmentedProcess ω T c₀ S k j).2) :
    augmentedProcess ω T c₀ S k (j + 1) =
      (openReachSet (topSites ω) (augmentedProcess ω T c₀ S k j).1 T ∪
        triangleTargets T (lowPt T j (augmentedProcess ω T c₀ S k j).1),
        (augmentedProcess ω T c₀ S k j).2 + 1) := by
  rw [augmentedProcess]
  exact ite_eq_left h

/-- When the guard fails, the next pair is the open reach, with the count unchanged. -/
private theorem augmentedProcess_succ_of_not (ω : Environment) (T : ℕ) (c₀ : ℝ)
    (S : Set Lattice) (k j : ℕ)
    (h : ¬ guardAt ω T c₀ k j (augmentedProcess ω T c₀ S k j).1
      (augmentedProcess ω T c₀ S k j).2) :
    augmentedProcess ω T c₀ S k (j + 1) =
      (openReachSet (topSites ω) (augmentedProcess ω T c₀ S k j).1 T,
        (augmentedProcess ω T c₀ S k j).2) := by
  rw [augmentedProcess]
  exact ite_eq_right h

/-- Membership at block `j + 1`: either in the open reach of the block `j` set, or the guard
holds and the site is a triangle target at the lowest point. -/
private theorem mem_succ_iff (ω : Environment) (T : ℕ) (c₀ : ℝ) (S : Set Lattice)
    (k j : ℕ) (z : Lattice) :
    z ∈ (augmentedProcess ω T c₀ S k (j + 1)).1 ↔
      z ∈ openReachSet (topSites ω) (augmentedProcess ω T c₀ S k j).1 T ∨
      (guardAt ω T c₀ k j (augmentedProcess ω T c₀ S k j).1
          (augmentedProcess ω T c₀ S k j).2 ∧
        z ∈ triangleTargets T (lowPt T j (augmentedProcess ω T c₀ S k j).1)) := by
  by_cases h : guardAt ω T c₀ k j (augmentedProcess ω T c₀ S k j).1
      (augmentedProcess ω T c₀ S k j).2
  · have e := congrArg Prod.fst (augmentedProcess_succ_of ω T c₀ S k j h)
    rw [e]
    constructor
    · rintro (hz | hz)
      · exact Or.inl hz
      · exact Or.inr ⟨h, hz⟩
    · rintro (hz | ⟨-, hz⟩)
      · exact Or.inl hz
      · exact Or.inr hz
  · have e := congrArg Prod.fst (augmentedProcess_succ_of_not ω T c₀ S k j h)
    rw [e]
    constructor
    · intro hz
      exact Or.inl hz
    · rintro (hz | ⟨hg, -⟩)
      · exact hz
      · exact absurd hg h

/-- The count at block `j + 1` when the guard holds. -/
private theorem snd_succ_of (ω : Environment) (T : ℕ) (c₀ : ℝ) (S : Set Lattice) (k j : ℕ)
    (h : guardAt ω T c₀ k j (augmentedProcess ω T c₀ S k j).1
      (augmentedProcess ω T c₀ S k j).2) :
    (augmentedProcess ω T c₀ S k (j + 1)).2 = (augmentedProcess ω T c₀ S k j).2 + 1 :=
  congrArg Prod.snd (augmentedProcess_succ_of ω T c₀ S k j h)

/-- The count at block `j + 1` when the guard fails. -/
private theorem snd_succ_of_not (ω : Environment) (T : ℕ) (c₀ : ℝ) (S : Set Lattice)
    (k j : ℕ)
    (h : ¬ guardAt ω T c₀ k j (augmentedProcess ω T c₀ S k j).1
      (augmentedProcess ω T c₀ S k j).2) :
    (augmentedProcess ω T c₀ S k (j + 1)).2 = (augmentedProcess ω T c₀ S k j).2 := by
  have e := congrArg Prod.snd (augmentedProcess_succ_of_not ω T c₀ S k j h)
  exact e

/-- A natural-number valued function that equals `f` where `p` holds and `g` elsewhere is
measurable when `p`, `f` and `g` are. -/
private theorem measurable_cond_nat {Ω : Type*} (m : MeasurableSpace Ω) {p : Ω → Prop}
    (hp : MeasurableSet[m] {ω | p ω}) {f g F : Ω → ℕ} (hf : Measurable[m] f)
    (hg : Measurable[m] g) (h1 : ∀ ω, p ω → F ω = f ω) (h0 : ∀ ω, ¬ p ω → F ω = g ω) :
    Measurable[m] F := by
  classical
  have hF : F = fun ω => if p ω then f ω else g ω := by
    funext ω
    by_cases h : p ω
    · rw [ite_eq_left h]
      exact h1 ω h
    · rw [ite_eq_right h]
      exact h0 ω h
  rw [hF]
  exact Measurable.ite hp hf hg

/-- One step of the induction, abstracted from `augmentedProcess`. If the pair `(X, K)` at
block `j` has measurable membership and count for the levels at most `j T`, and the pair
`(X', K')` is obtained by the augmentation rule, then `(X', K')` is measurable for the
levels at most `j T + T`. The guard is split according to the value `a` of the lowest
point's first coordinate: each piece is an event at the fixed site `(a, j T - a)`. -/
private theorem measurable_step (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ) (k j : ℕ)
    (X X' : Environment → Set Lattice) (K K' : Environment → ℕ)
    (hXlev : ∀ ω, X ω ⊆ levelSet ((j : ℤ) * T))
    (hX : ∀ z : Lattice, MeasurableSet[levelsAtMost ((j : ℤ) * T)] {ω | z ∈ X ω})
    (hK : Measurable[levelsAtMost ((j : ℤ) * T)] K)
    (hX' : ∀ ω z, z ∈ X' ω ↔ z ∈ openReachSet (topSites ω) (X ω) T ∨
      (guardAt ω T c₀ k j (X ω) (K ω) ∧ z ∈ triangleTargets T (lowPt T j (X ω))))
    (hK1 : ∀ ω, guardAt ω T c₀ k j (X ω) (K ω) → K' ω = K ω + 1)
    (hK0 : ∀ ω, ¬ guardAt ω T c₀ k j (X ω) (K ω) → K' ω = K ω) :
    (∀ z : Lattice, MeasurableSet[levelsAtMost ((j : ℤ) * T + T)] {ω | z ∈ X' ω}) ∧
      Measurable[levelsAtMost ((j : ℤ) * T + T)] K' := by
  have hjT : (j : ℤ) * T ≤ (j : ℤ) * T + T := by omega
  -- The first coordinate of the lowest point is measurable at level `j T`.
  have hmax : Measurable[levelsAtMost ((j : ℤ) * T)] fun ω => maxFirst (X ω) :=
    measurable_maxFirst_of_measurableSet_mem _ X hX
  have hLow : ∀ a : ℤ, MeasurableSet[levelsAtMost ((j : ℤ) * T + T)]
      {ω : Environment | maxFirst (X ω) = a} := fun a =>
    measurableSet_levels_mono hjT (hmax (measurableSet_singleton a))
  have hKlt : MeasurableSet[levelsAtMost ((j : ℤ) * T + T)] {ω : Environment | K ω < k} :=
    measurableSet_levels_mono hjT (hK (MeasurableSet.of_discrete : MeasurableSet {n : ℕ | n < k}))
  -- The triangle event at the fixed site `(a, j T - a)` reads levels up to `j T + T`.
  have hTri : ∀ a : ℤ, MeasurableSet[levelsAtMost ((j : ℤ) * T + T)]
      {ω : Environment | IsTriangle ω T c₀ ((a, (j : ℤ) * T - a) : Lattice)} := fun a =>
    measurableSet_levels_mono
      (by show a + ((j : ℤ) * T - a) + (T : ℤ) ≤ (j : ℤ) * T + T; omega)
      (measurableSet_isTriangle_levelsAtMost T hT c₀ ((a, (j : ℤ) * T - a) : Lattice))
  -- The guard together with any condition on the first coordinate of the lowest point.
  have hGQ : ∀ Q : ℤ → Prop, MeasurableSet[levelsAtMost ((j : ℤ) * T + T)]
      {ω : Environment | guardAt ω T c₀ k j (X ω) (K ω) ∧ Q (maxFirst (X ω))} := by
    intro Q
    have hEq : {ω : Environment | guardAt ω T c₀ k j (X ω) (K ω) ∧ Q (maxFirst (X ω))} =
        ⋃ a : ℤ, {ω : Environment | maxFirst (X ω) = a} ∩
          ({ω : Environment | K ω < k} ∩
            ({ω : Environment | ((a, (j : ℤ) * T - a) : Lattice) ∈ X ω} ∩
              ({ω : Environment | IsTriangle ω T c₀ ((a, (j : ℤ) * T - a) : Lattice)} ∩
                {_ω : Environment | Q a}))) := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨⟨hKk, hr, ht⟩, hQ⟩
        exact ⟨_, rfl, hKk, hr, ht, hQ⟩
      · rintro ⟨a, rfl, hKk, hr, ht, hQ⟩
        exact ⟨⟨hKk, hr, ht⟩, hQ⟩
    rw [hEq]
    refine MeasurableSet.iUnion fun a => ?_
    exact (hLow a).inter (hKlt.inter
      ((measurableSet_levels_mono hjT (hX ((a, (j : ℤ) * T - a) : Lattice))).inter
        ((hTri a).inter (MeasurableSet.const _))))
  have hG : MeasurableSet[levelsAtMost ((j : ℤ) * T + T)]
      {ω : Environment | guardAt ω T c₀ k j (X ω) (K ω)} := by
    have e : {ω : Environment | guardAt ω T c₀ k j (X ω) (K ω) ∧ True} =
        {ω : Environment | guardAt ω T c₀ k j (X ω) (K ω)} := by
      ext ω
      simp only [mem_ofPred_eq, and_true]
    exact (hGQ fun _ => True).congr e
  -- Membership at the next block: open reach, or guard together with target.
  have hmem : ∀ z : Lattice, MeasurableSet[levelsAtMost ((j : ℤ) * T + T)]
      {ω : Environment | z ∈ X' ω} := by
    intro z
    have hEq : {ω : Environment | z ∈ X' ω} =
        {ω : Environment | z ∈ openReachSet (topSites ω) (X ω) T} ∪
        {ω : Environment | guardAt ω T c₀ k j (X ω) (K ω) ∧
          z ∈ triangleTargets T (lowPt T j (X ω))} := by
      ext ω
      exact hX' ω z
    rw [hEq]
    exact (measurableSet_mem_openReachSet_levelsAtMost ((j : ℤ) * T) T X hXlev hX z).union
      (hGQ fun a => z ∈ triangleTargets T ((a, (j : ℤ) * T - a) : Lattice))
  -- The count at the next block.
  have hKmono : Measurable[levelsAtMost ((j : ℤ) * T + T)] K :=
    hK.mono (levelsAtMost_mono hjT) le_rfl
  exact ⟨hmem, measurable_cond_nat _ hG (hKmono.add_const 1) hKmono hK1 hK0⟩

/-! ## The statements -/

/-- Fix `1 ≤ T`, a start set on level `0` and a cap `k`. For the weights at levels at most
`j T`, membership of each site in the occupied set `X_j` and the count `K_j` are
measurable. This is the measurability of the block-`j` state of the augmented process.
It supports the freezing step of the augmentation argument.
The proof is an induction on `j` through `measurable_step`. -/
theorem measurable_augmentedProcess (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ) (S : Set Lattice)
    (hS : S ⊆ levelSet 0) (k j : ℕ) :
    (∀ z : Lattice, MeasurableSet[levelsAtMost ((j : ℤ) * T)]
      {ω : Environment | z ∈ (augmentedProcess ω T c₀ S k j).1}) ∧
    Measurable[levelsAtMost ((j : ℤ) * T)]
      (fun ω : Environment => (augmentedProcess ω T c₀ S k j).2) := by
  induction j with
  | zero =>
    have e : ∀ ω : Environment, augmentedProcess ω T c₀ S k 0 = (S, 0) := fun ω => by
      rw [augmentedProcess]
    refine ⟨fun z => ?_, ?_⟩
    · have h : {ω : Environment | z ∈ (augmentedProcess ω T c₀ S k 0).1} =
          {_ω : Environment | z ∈ S} :=
        Set.ext fun ω => Iff.of_eq (congrArg (fun p : Set Lattice × ℕ => z ∈ p.1) (e ω))
      rw [h]
      exact MeasurableSet.const _
    · have h : (fun ω : Environment => (augmentedProcess ω T c₀ S k 0).2) = fun _ => 0 :=
        funext fun ω => congrArg Prod.snd (e ω)
      rw [h]
      exact measurable_const
  | succ j ih =>
    have e : ((j + 1 : ℕ) : ℤ) * (T : ℤ) = (j : ℤ) * T + T := by
      push_cast
      ring
    rw [e]
    obtain ⟨hX, hK⟩ := ih
    exact measurable_step T hT c₀ k j (fun ω => (augmentedProcess ω T c₀ S k j).1)
      (fun ω => (augmentedProcess ω T c₀ S k (j + 1)).1)
      (fun ω => (augmentedProcess ω T c₀ S k j).2)
      (fun ω => (augmentedProcess ω T c₀ S k (j + 1)).2)
      (fun ω => augmentedProcess_subset_levelSet ω T c₀ S hS k j) hX hK
      (fun ω z => mem_succ_iff ω T c₀ S k j z)
      (fun ω h => snd_succ_of ω T c₀ S k j h)
      (fun ω h => snd_succ_of_not ω T c₀ S k j h)

/-- The first coordinate of the lowest point of the block-`j` set is measurable for the
weights at levels at most `j T`. -/
theorem measurable_maxFirst_augmentedProcess (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ)
    (S : Set Lattice) (hS : S ⊆ levelSet 0) (k j : ℕ) :
    Measurable[levelsAtMost ((j : ℤ) * T)]
      (fun ω : Environment => maxFirst (augmentedProcess ω T c₀ S k j).1) :=
  measurable_maxFirst_of_measurableSet_mem (levelsAtMost ((j : ℤ) * T))
    (fun ω => (augmentedProcess ω T c₀ S k j).1)
    (measurable_augmentedProcess T hT c₀ S hS k j).1

/-- The event that there is a triangle at the lowest point of the block-`j` set is
measurable for the weights at levels at most `j T + T`. It is the countable union, over the
first coordinate `a` of the lowest point, of "the lowest point has first coordinate `a`"
(levels at most `j T`) and "there is a triangle at `(a, j T - a)`" (levels at most
`j T + T`). -/
theorem measurableSet_isTriangle_lowestPoint (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ)
    (S : Set Lattice) (hS : S ⊆ levelSet 0) (k j : ℕ) :
    MeasurableSet[levelsAtMost ((j : ℤ) * T + T)] {ω : Environment | IsTriangle ω T c₀
      (maxFirst (augmentedProcess ω T c₀ S k j).1,
        (j : ℤ) * T - maxFirst (augmentedProcess ω T c₀ S k j).1)} := by
  have hjT : (j : ℤ) * T ≤ (j : ℤ) * T + T := by omega
  have hmax := measurable_maxFirst_augmentedProcess T hT c₀ S hS k j
  -- Split according to the value `a` of the first coordinate of the lowest point.
  have hEq : {ω : Environment | IsTriangle ω T c₀
        (maxFirst (augmentedProcess ω T c₀ S k j).1,
          (j : ℤ) * T - maxFirst (augmentedProcess ω T c₀ S k j).1)} =
      ⋃ a : ℤ, {ω : Environment | maxFirst (augmentedProcess ω T c₀ S k j).1 = a} ∩
        {ω : Environment | IsTriangle ω T c₀ ((a, (j : ℤ) * T - a) : Lattice)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      exact ⟨_, rfl, h⟩
    · rintro ⟨a, rfl, h⟩
      exact h
  rw [hEq]
  refine MeasurableSet.iUnion fun a => ?_
  have h1 : MeasurableSet[levelsAtMost ((j : ℤ) * T + T)]
      {ω : Environment | maxFirst (augmentedProcess ω T c₀ S k j).1 = a} :=
    measurableSet_levels_mono hjT (hmax (measurableSet_singleton a))
  have hTri := measurableSet_isTriangle_levelsAtMost T hT c₀ ((a, (j : ℤ) * T - a) : Lattice)
  exact h1.inter (measurableSet_levels_mono
    (by show a + ((j : ℤ) * T - a) + (T : ℤ) ≤ (j : ℤ) * T + T; omega) hTri)

end LPPDifferentiability
