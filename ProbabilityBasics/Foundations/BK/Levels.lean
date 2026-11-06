/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Levels and rounding up in one ordered coordinate

Van den Berg and Kesten (1985), Theorem 3.3, treats finite products of bits; the levels here let
an ordered coordinate take values in a suitable ordered space.

Let `X` be a linear order with the order topology, a countable base and the Borel
`σ`-algebra, and let `ν` be a finite measure on `X`.

* `IsLevelSet ν D`: `D` is a countable set of "levels" that contains every atom of `ν`, has a
  level in `(x, y]` whenever `x < y`, and has a level below every point.
* `exists_isLevelSet`: every finite measure has a level set.
* `roundUp Λ x`: for a finite set `Λ` of levels, the smallest level at or above `x`, or `⊤` if
  there is none.
* `rankUp Λ x`: the number of levels strictly below `x`; `levelOfRank Λ` sends a rank back to the
  rounded value, so that `levelOfRank Λ (rankUp Λ x) = roundUp Λ x`.
* Order facts: `x ≤ roundUp Λ x`; `roundUp Λ x` is below every level above `x`; it decreases when
  levels are added and increases with `x`; `rankUp Λ` is increasing and measurable.

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985).
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityBasics.BK

section LevelSets

variable {X : Type*} [MeasurableSpace X] [LinearOrder X]

/-- A set `D` of levels for the law `ν` on the ordered space `X`: `D` is countable, contains every
atom of `ν`, has a level in `(x, y]` whenever `x < y`, and has a level below every point
(this is not in the paper). -/
structure IsLevelSet (ν : Measure X) (D : Set X) : Prop where
  /-- The set of levels is countable. -/
  countable : D.Countable
  /-- Every atom of `ν` is a level. -/
  atoms : ∀ x, 0 < ν {x} → x ∈ D
  /-- Between any two points `x < y` there is a level in `(x, y]`. -/
  between : ∀ x y, x < y → ∃ d ∈ D, x < d ∧ d ≤ y
  /-- Every point has a level at or below it. -/
  coinitial : ∀ x, ∃ d ∈ D, d ≤ x

/-- Every finite measure on `X` has a level set. Take a countable dense set, the points with an
immediate predecessor, the atoms, and the least element if there is one. -/
theorem exists_isLevelSet [TopologicalSpace X] [OrderTopology X] [SecondCountableTopology X]
    [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] : ∃ D : Set X, IsLevelSet ν D := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense X
  have hPc : {y : X | ∃ x, x ⋖ y}.Countable := countable_setOfPred_covBy_left
  have hAc : {x : X | 0 < ν {x}}.Countable :=
    Measure.countable_meas_level_set_pos (μ := ν) (g := id) measurable_id
  have hLc : {x : X | ∀ y, x ≤ y}.Countable := by
    refine Set.Subsingleton.countable fun x hx y hy => ?_
    exact le_antisymm (hx y) (hy x)
  have between : ∀ x y : X, x < y → ∃ d ∈ S ∪ {y : X | ∃ x, x ⋖ y} ∪ {x : X | 0 < ν {x}} ∪
      {x : X | ∀ y, x ≤ y}, x < d ∧ d ≤ y := by
    intro x y hxy
    by_cases hne : (Ioo x y).Nonempty
    · obtain ⟨d, hdS, hd⟩ := hSd.exists_mem_open isOpen_Ioo hne
      exact ⟨d, mem_union_left _ (mem_union_left _ (mem_union_left _ hdS)), hd.1, hd.2.le⟩
    · have hcov : x ⋖ y :=
        covBy_iff_Ioo_eq.2 ⟨hxy, Set.not_nonempty_iff_eq_empty.1 hne⟩
      exact ⟨y, mem_union_left _ (mem_union_left _ (mem_union_right _
        (⟨x, hcov⟩ : ∃ x, x ⋖ y))), hxy, le_rfl⟩
  refine ⟨S ∪ {y : X | ∃ x, x ⋖ y} ∪ {x : X | 0 < ν {x}} ∪ {x : X | ∀ y, x ≤ y},
    ⟨((hSc.union hPc).union hAc).union hLc, fun x hx => ?_, between, fun x => ?_⟩⟩
  · exact mem_union_left _ (mem_union_right _ hx)
  · by_cases hx : ∀ y, x ≤ y
    · exact ⟨x, mem_union_right _ hx, le_rfl⟩
    · obtain ⟨y, hy⟩ := not_forall.1 hx
      obtain ⟨d, hd, -, hdx⟩ := between y x (not_le.1 hy)
      exact ⟨d, hd, hdx⟩

end LevelSets

section Rounding

variable {X : Type*} [LinearOrder X]

/-- Rounding up to a finite set `Λ` of levels: the smallest level of `Λ` at or above `x`, and `⊤`
if `x` is above every level. -/
noncomputable def roundUp (Λ : Finset X) (x : X) : WithTop X :=
  (Λ.filter (x ≤ ·)).min

/-- The rank of `x` among the finite set `Λ` of levels: the number of levels strictly below `x`. -/
noncomputable def rankUp (Λ : Finset X) (x : X) : Fin (Λ.card + 1) :=
  ⟨(Λ.filter (· < x)).card, Nat.lt_succ_of_le (Finset.card_le_card (Finset.filter_subset _ _))⟩

/-- The rounded value belonging to a rank: the `k`-th smallest level (counting from `0`) if
`k < Λ.card`, and `⊤` if `k = Λ.card`. -/
noncomputable def levelOfRank (Λ : Finset X) (k : Fin (Λ.card + 1)) : WithTop X :=
  if h : k.val < Λ.card then ((Λ.orderEmbOfFin rfl ⟨k.val, h⟩ : X) : WithTop X) else ⊤

/-- A point lies below its rounded value. -/
theorem le_roundUp (Λ : Finset X) (x : X) : (x : WithTop X) ≤ roundUp Λ x := by
  unfold roundUp
  refine Finset.le_min fun d hd => ?_
  exact WithTop.coe_le_coe.2 (Finset.mem_filter.1 hd).2

/-- The rounded value is below every level that is at or above the point. -/
theorem roundUp_le {Λ : Finset X} {x d : X} (hd : d ∈ Λ) (hxd : x ≤ d) :
    roundUp Λ x ≤ (d : WithTop X) :=
  Finset.min_le (Finset.mem_filter.2 ⟨hd, hxd⟩)

/-- Adding levels can only lower the rounded value. -/
theorem roundUp_anti {Λ Λ' : Finset X} (h : Λ ⊆ Λ') (x : X) : roundUp Λ' x ≤ roundUp Λ x :=
  Finset.min_mono (Finset.filter_subset_filter _ h)

/-- Rounding up is increasing in the point. -/
theorem roundUp_mono (Λ : Finset X) {x y : X} (hxy : x ≤ y) : roundUp Λ x ≤ roundUp Λ y :=
  Finset.min_mono fun _ hd =>
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hd).1, hxy.trans (Finset.mem_filter.1 hd).2⟩

/-- The rank is increasing in the point. -/
theorem rankUp_mono (Λ : Finset X) {x y : X} (hxy : x ≤ y) : rankUp Λ x ≤ rankUp Λ y := by
  show (Λ.filter (· < x)).card ≤ (Λ.filter (· < y)).card
  exact Finset.card_le_card fun d hd =>
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hd).1, lt_of_lt_of_le (Finset.mem_filter.1 hd).2 hxy⟩

/-- Larger ranks give larger rounded values. -/
theorem levelOfRank_strictMono (Λ : Finset X) : StrictMono (levelOfRank Λ) := by
  intro k l hkl
  have hkl' : k.val < l.val := Fin.lt_def.1 hkl
  have hl' : l.val < Λ.card + 1 := l.isLt
  have hk : k.val < Λ.card := by omega
  unfold levelOfRank
  rw [dite_eq_left hk]
  by_cases hl : l.val < Λ.card
  · rw [dite_eq_left hl]
    exact WithTop.coe_lt_coe.2 ((Λ.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.2 hkl'))
  · rw [dite_eq_right hl]
    exact WithTop.coe_lt_top _

/-- Among the levels of `Λ`, exactly `j` are strictly below the `j`-th smallest one. -/
private theorem card_filter_lt_orderEmbOfFin (Λ : Finset X) (j : Fin Λ.card) :
    (Λ.filter (· < Λ.orderEmbOfFin rfl j)).card = j.val := by
  have hset : Λ.filter (· < Λ.orderEmbOfFin rfl j) =
      (Finset.Iio j).image (Λ.orderEmbOfFin rfl) := by
    ext d
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hd, hlt⟩
      obtain ⟨m, rfl⟩ : d ∈ Set.range (Λ.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hd
      exact ⟨m, Finset.mem_Iio.2 ((Λ.orderEmbOfFin rfl).lt_iff_lt.1 hlt), rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _,
        (Λ.orderEmbOfFin rfl).lt_iff_lt.2 (Finset.mem_Iio.1 hm)⟩
  rw [hset, Finset.card_image_of_injective _ (Λ.orderEmbOfFin rfl).injective, Fin.card_Iio]

/-- The rank recovers the rounded value: the level of the rank of `x` is `roundUp Λ x`. -/
theorem levelOfRank_rankUp (Λ : Finset X) (x : X) :
    levelOfRank Λ (rankUp Λ x) = roundUp Λ x := by
  by_cases hne : (Λ.filter (x ≤ ·)).Nonempty
  · obtain ⟨m, hm⟩ := Finset.min_of_nonempty hne
    obtain ⟨hmΛ, hxm⟩ := Finset.mem_filter.1 (Finset.mem_of_min hm)
    obtain ⟨j, hj⟩ : m ∈ Set.range (Λ.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hmΛ
    have hbelow : Λ.filter (· < m) = Λ.filter (· < x) := by
      ext d
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨hd, hdm⟩
        refine ⟨hd, not_le.1 fun hxd => ?_⟩
        exact absurd (Finset.min_le_of_eq (Finset.mem_filter.2 ⟨hd, hxd⟩) hm) (not_le.2 hdm)
      · rintro ⟨hd, hdx⟩
        exact ⟨hd, lt_of_lt_of_le hdx hxm⟩
    have hjk : j.val = (Λ.filter (· < x)).card := by
      rw [← hbelow, ← hj]
      exact (card_filter_lt_orderEmbOfFin Λ j).symm
    have hround : roundUp Λ x = (m : WithTop X) := hm
    have hlt : (rankUp Λ x).val < Λ.card := by
      have hrank : (rankUp Λ x).val = j.val := hjk.symm
      rw [hrank]
      exact j.isLt
    have hfin : (⟨(rankUp Λ x).val, hlt⟩ : Fin Λ.card) = j := Fin.ext hjk.symm
    rw [hround]
    unfold levelOfRank
    rw [dite_eq_left hlt, hfin, hj]
  · have hempty : Λ.filter (x ≤ ·) = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    have hround : roundUp Λ x = ⊤ := by
      rw [roundUp, hempty, Finset.min_empty]
    have hall : Λ.filter (· < x) = Λ := by
      ext d
      rw [Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · intro hd
        refine ⟨hd, not_le.1 fun hxd => ?_⟩
        have hmem : d ∈ Λ.filter (x ≤ ·) := Finset.mem_filter.2 ⟨hd, hxd⟩
        rw [hempty] at hmem
        exact Finset.notMem_empty d hmem
    have hk : (rankUp Λ x).val = Λ.card := by
      show (Λ.filter (· < x)).card = Λ.card
      rw [hall]
    rw [hround]
    unfold levelOfRank
    rw [dite_eq_right (by omega)]

end Rounding

section Measurability

variable {X : Type*} [MeasurableSpace X] [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
  [BorelSpace X]

/-- The rank is a measurable function of the point: its fibres are finite unions of intervals. -/
theorem measurable_rankUp (Λ : Finset X) : Measurable (rankUp Λ) := by
  have hcount : Measurable fun x : X => (Λ.filter (· < x)).card := by
    have hsum : (fun x : X => (Λ.filter (· < x)).card) =
        fun x => ∑ d ∈ Λ, (Ioi d).indicator (fun _ => (1 : ℕ)) x := by
      funext x
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases h : d < x <;> simp [h]
    rw [hsum]
    exact Finset.measurable_sum _ fun d _ => measurable_const.indicator measurableSet_Ioi
  refine measurable_to_countable' fun k => ?_
  have hfibre : rankUp Λ ⁻¹' {k} = (fun x : X => (Λ.filter (· < x)).card) ⁻¹' {k.val} := by
    ext x
    exact Fin.ext_iff
  rw [hfibre]
  exact hcount (measurableSet_singleton _)

end Measurability

end ProbabilityBasics.BK
