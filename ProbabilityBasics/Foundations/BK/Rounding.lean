/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Foundations.BK.Levels

/-!
# Rounding every coordinate up to finitely many levels

Van den Berg and Kesten (1985), Theorem 3.3, treats finite products of bits. This file rounds
each coordinate of a finite ordered product up to finitely many levels; the limit statements are
in later modules.

Let `ι` be a finite index type and `E i` a linear order for each `i` (with the order topology and
the Borel `σ`-algebra when measurability is discussed). `∀ i, E i` carries the coordinatewise order,
and "increasing" means `IsUpperSet`. Let `Λ i m` be a finite set of levels in `E i` for each `m`,
`N : ι → ℕ` say how many levels each coordinate uses, and `s` be the finite set of "exact"
coordinates, which are not rounded.

* `boxAbove ρ`: the points that lie coordinatewise at or above `ρ`, where `ρ i` may be `⊤`.
* `roundedSet Λ N s A`: the points `ω` such that every point above the rounded version of `ω` is in
  `A`. The rounded version keeps `ω i` for `i ∈ s` and replaces `ω i` by `roundUp (Λ i (N i)) (ω i)`
  for `i ∉ s`.
* `roundedSet_univ`, `subset_roundedSet`: with every coordinate exact the set is `A`, and `A` is
  always inside it, for increasing `A`.
* `isUpperSet_roundedSet`, `measurableSet_roundedSet`: the set is increasing, and measurable when
  `A` is measurable and increasing.
* `roundCoord k Λk A` and `roundedSet_update`: rounding coordinate `k` to the levels `Λ k m` is the
  same as taking `roundCoord` of the set with coordinate `k` made exact.
* `monotone_image_range`, `iUnion_image_range`: the finite level sets `(range m).image e` that
  enumerate a countable set increase to it.

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985).
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityBasics.BK

section LevelFamily

variable {X : Type*} [LinearOrder X]

/-- The finite sets of the first `m` terms of a sequence increase with `m`
(`Λ i m = (range m).image (e i)`). -/
theorem monotone_image_range (e : ℕ → X) : Monotone fun m => (Finset.range m).image e :=
  fun _ _ h => Finset.image_subset_image (Finset.range_mono h)

/-- The union of the finite sets of the first `m` terms of a sequence is its range (the
union of the `Λ i m` is the level set `D i`). -/
theorem iUnion_image_range (e : ℕ → X) :
    ⋃ m, (((Finset.range m).image e : Finset X) : Set X) = Set.range e := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_image, Finset.mem_range, Set.mem_range]
  constructor
  · rintro ⟨m, n, -, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n + 1, n, Nat.lt_succ_self n, rfl⟩

end LevelFamily

section Boxes

variable {ι : Type*} {E : ι → Type*} [∀ i, LinearOrder (E i)]

/-- The points of `∀ i, E i` that lie coordinatewise at or above `ρ`, where each bound `ρ i` is an
element of `E i` or `⊤`. If some `ρ i = ⊤`, the set is empty. -/
def boxAbove (ρ : ∀ i, WithTop (E i)) : Set (∀ i, E i) :=
  {ω | ∀ i, ρ i ≤ (ω i : WithTop (E i))}

/-- Membership in `boxAbove`, unfolded. -/
theorem mem_boxAbove {ρ : ∀ i, WithTop (E i)} {ω : ∀ i, E i} :
    ω ∈ boxAbove ρ ↔ ∀ i, ρ i ≤ (ω i : WithTop (E i)) :=
  Iff.rfl

/-- With bounds that are all points, `boxAbove` is the closed upper interval. -/
theorem boxAbove_coe (c : ∀ i, E i) : boxAbove (fun i => (c i : WithTop (E i))) = Set.Ici c := by
  ext ω
  simp only [mem_boxAbove, Set.mem_Ici, Pi.le_def, WithTop.coe_le_coe]

/-- Raising the bounds shrinks the box. -/
theorem boxAbove_anti {ρ ρ' : ∀ i, WithTop (E i)} (h : ∀ i, ρ i ≤ ρ' i) :
    boxAbove ρ' ⊆ boxAbove ρ :=
  fun _ hω => mem_boxAbove.2 fun i => (h i).trans (mem_boxAbove.1 hω i)

/-- The box is empty as soon as one bound is `⊤`. -/
theorem boxAbove_eq_empty {ρ : ∀ i, WithTop (E i)} {i : ι} (h : ρ i = ⊤) : boxAbove ρ = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun ω hω => ?_
  have hi : ρ i ≤ (ω i : WithTop (E i)) := mem_boxAbove.1 hω i
  rw [h] at hi
  exact WithTop.coe_ne_top (top_le_iff.1 hi)

/-- For an increasing set `A`, the box above the point `c` lies in `A` exactly when `c ∈ A`. -/
theorem boxAbove_subset_iff {A : Set (∀ i, E i)} (hA : IsUpperSet A) (c : ∀ i, E i) :
    boxAbove (fun i => (c i : WithTop (E i))) ⊆ A ↔ c ∈ A := by
  rw [boxAbove_coe]
  exact ⟨fun h => h (show c ∈ Set.Ici c from Set.mem_Ici.2 le_rfl), fun h _ hx => hA (Set.mem_Ici.1 hx) h⟩

end Boxes

section Rounded

variable {ι : Type*} [DecidableEq ι] {E : ι → Type*} [∀ i, LinearOrder (E i)]

/-- Round every coordinate outside `s` up to the levels `Λ i (N i)`, keep the coordinates in `s`
exact, and ask that the whole box above the result lies in `A`. -/
noncomputable def roundedSet (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ) (s : Finset ι)
    (A : Set (∀ i, E i)) : Set (∀ i, E i) :=
  {ω | boxAbove (fun i => if i ∈ s then (ω i : WithTop (E i))
    else roundUp (Λ i (N i)) (ω i)) ⊆ A}

/-- Remove the rounding of coordinate `k`: the points all of whose upper moves of coordinate `k`, to
at or above the rounded value `roundUp Λk (ω k)`, stay in `A`. -/
noncomputable def roundCoord (k : ι) (Λk : Finset (E k)) (A : Set (∀ i, E i)) :
    Set (∀ i, E i) :=
  {ω | ∀ x : E k, roundUp Λk (ω k) ≤ (x : WithTop (E k)) → Function.update ω k x ∈ A}

/-- The rounded version of `ω` used in `roundedSet`: coordinates in `s` exact, the others rounded up
to `Λ i (N i)`. Only used in proofs. -/
private noncomputable def roundedPoint (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ) (s : Finset ι)
    (ω : ∀ i, E i) (i : ι) : WithTop (E i) :=
  if i ∈ s then (ω i : WithTop (E i)) else roundUp (Λ i (N i)) (ω i)

private theorem mem_roundedSet {Λ : ∀ i, ℕ → Finset (E i)} {N : ι → ℕ} {s : Finset ι}
    {A : Set (∀ i, E i)} {ω : ∀ i, E i} :
    ω ∈ roundedSet Λ N s A ↔ boxAbove (roundedPoint Λ N s ω) ⊆ A :=
  Iff.rfl

/-- A point lies in `roundCoord k Λk A` exactly when every move of coordinate `k` to a value at or
above its rounded value stays in `A`. This is the definition, stated as a lemma. -/
theorem mem_roundCoord {k : ι} {Λk : Finset (E k)} {A : Set (∀ i, E i)}
    {ω : ∀ i, E i} :
    ω ∈ roundCoord k Λk A ↔
      ∀ x : E k, roundUp Λk (ω k) ≤ (x : WithTop (E k)) → Function.update ω k x ∈ A :=
  Iff.rfl

/-- Raising a point raises its rounded version coordinatewise. -/
private theorem roundedPoint_mono (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ) (s : Finset ι)
    {ω ω' : ∀ i, E i} (h : ω ≤ ω') (i : ι) :
    roundedPoint Λ N s ω i ≤ roundedPoint Λ N s ω' i := by
  by_cases hi : i ∈ s
  · simp only [roundedPoint, hi, ↓reduceIte]
    exact WithTop.coe_le_coe.2 (h i)
  · simp only [roundedPoint, hi, ↓reduceIte]
    exact roundUp_mono _ (h i)

/-- A point lies coordinatewise below its rounded version. -/
private theorem le_roundedPoint (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ) (s : Finset ι)
    (ω : ∀ i, E i) (i : ι) : (ω i : WithTop (E i)) ≤ roundedPoint Λ N s ω i := by
  by_cases hi : i ∈ s
  · simp only [roundedPoint, hi, ↓reduceIte]
    exact le_rfl
  · simp only [roundedPoint, hi, ↓reduceIte]
    exact le_roundUp _ _

/-- The set `roundedSet Λ N s A` is increasing, for every `A`. -/
theorem isUpperSet_roundedSet (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ) (s : Finset ι)
    (A : Set (∀ i, E i)) : IsUpperSet (roundedSet Λ N s A) :=
  fun _ _ h hω => mem_roundedSet.2
    (Set.Subset.trans (boxAbove_anti (roundedPoint_mono Λ N s h)) (mem_roundedSet.1 hω))

/-- For increasing `A`, the set `A` lies inside `roundedSet Λ N s A`. -/
theorem subset_roundedSet (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ) (s : Finset ι)
    {A : Set (∀ i, E i)} (hA : IsUpperSet A) : A ⊆ roundedSet Λ N s A := by
  intro ω hω
  refine mem_roundedSet.2 fun ω' hω' => ?_
  have hle : ω ≤ ω' := fun i =>
    WithTop.coe_le_coe.1 ((le_roundedPoint Λ N s ω i).trans (mem_boxAbove.1 hω' i))
  exact hA hle hω

/-- With every coordinate exact, `roundedSet` is the set `A` itself, for increasing `A`. -/
theorem roundedSet_univ [Fintype ι] (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ)
    {A : Set (∀ i, E i)} (hA : IsUpperSet A) : roundedSet Λ N Finset.univ A = A := by
  ext ω
  have hρ : roundedPoint Λ N Finset.univ ω = fun i => (ω i : WithTop (E i)) := by
    funext i
    simp only [roundedPoint, Finset.mem_univ, ↓reduceIte]
  rw [mem_roundedSet, hρ]
  exact boxAbove_subset_iff hA ω

/-- Fixing the bound of one coordinate: the box above `ρ` lies in `A` exactly when, for every point
`x` at or above `ρ k`, the box above `ρ` with `k`-th bound replaced by `x` lies in `A` (the second
boxes together cover the first one, taking `x = ω k`). -/
private theorem boxAbove_subset_iff_forall_update (ρ : ∀ i, WithTop (E i)) (k : ι)
    (A : Set (∀ i, E i)) :
    boxAbove ρ ⊆ A ↔
      ∀ x : E k, ρ k ≤ (x : WithTop (E k)) →
        boxAbove (Function.update ρ k (x : WithTop (E k))) ⊆ A := by
  constructor
  · intro h x hx
    refine Set.Subset.trans (b := boxAbove ρ) (fun ω hω => mem_boxAbove.2 fun i => ?_) h
    have hi := mem_boxAbove.1 hω i
    rcases eq_or_ne i k with rfl | hik
    · rw [Function.update_self] at hi
      exact hx.trans hi
    · rwa [Function.update_of_ne hik] at hi
  · intro h ω hω
    refine h (ω k) (mem_boxAbove.1 hω k) (mem_boxAbove.2 fun i => ?_)
    rcases eq_or_ne i k with rfl | hik
    · rw [Function.update_self]
    · rw [Function.update_of_ne hik]
      exact mem_boxAbove.1 hω i

/-- Making coordinate `k` exact and then rounding it with `roundCoord` is the same as rounding it to
the levels `Λ k m` from the start. This holds for every set `A`; the assumption
`k ∉ s` is needed. -/
theorem roundedSet_update (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ) {s : Finset ι} {k : ι}
    (hk : k ∉ s) (m : ℕ) (A : Set (∀ i, E i)) :
    roundedSet Λ (Function.update N k m) s A =
      roundCoord k (Λ k m) (roundedSet Λ N (insert k s) A) := by
  ext ω
  have hρ : ∀ x : E k, roundedPoint Λ N (insert k s) (Function.update ω k x) =
      Function.update (roundedPoint Λ (Function.update N k m) s ω) k (x : WithTop (E k)) := by
    intro x
    funext i
    rcases eq_or_ne i k with rfl | hik
    · simp only [roundedPoint, Finset.mem_insert_self, ↓reduceIte, Function.update_self]
    · simp only [roundedPoint, Finset.mem_insert, hik, false_or, Function.update_of_ne hik]
  have hρk : roundedPoint Λ (Function.update N k m) s ω k = roundUp (Λ k m) (ω k) := by
    simp only [roundedPoint, hk, ↓reduceIte, Function.update_self]
  refine (mem_roundedSet.trans (boxAbove_subset_iff_forall_update _ k A)).trans ?_
  refine Iff.trans ?_ mem_roundCoord.symm
  refine forall_congr' fun x => ?_
  rw [hρk, mem_roundedSet, hρ x]

/-- The rounded point of `ω` when no coordinate is `⊤`: coordinates in `s` stay, the others are
replaced by their rounded values. Only used in proofs. -/
private noncomputable def roundedValue (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ) (s : Finset ι)
    (ω : ∀ i, E i) (i : ι) : E i :=
  if i ∈ s then ω i else (roundUp (Λ i (N i)) (ω i)).untopD (ω i)

/-- Away from `⊤`, the rounded point is the coercion of `roundedValue`. -/
private theorem roundedPoint_eq_coe (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ) (s : Finset ι)
    {ω : ∀ i, E i} (hne : ∀ i, roundedPoint Λ N s ω i ≠ ⊤) :
    roundedPoint Λ N s ω = fun i => (roundedValue Λ N s ω i : WithTop (E i)) := by
  funext i
  have hi := hne i
  by_cases his : i ∈ s
  · simp only [roundedPoint, roundedValue, his, ↓reduceIte]
  · simp only [roundedPoint, roundedValue, his, ↓reduceIte] at hi ⊢
    generalize roundUp (Λ i (N i)) (ω i) = r at hi ⊢
    induction r using WithTop.recTopCoe with
    | top => exact absurd rfl hi
    | coe a => rfl

/-- For increasing `A`, a point is in `roundedSet` exactly when some rounded coordinate is `⊤`
(the box is empty) or the point `roundedValue` is in `A` (the box is a closed upper interval). -/
private theorem mem_roundedSet_iff (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ) (s : Finset ι)
    {A : Set (∀ i, E i)} (hA : IsUpperSet A) (ω : ∀ i, E i) :
    ω ∈ roundedSet Λ N s A ↔
      (∃ i, roundedPoint Λ N s ω i = ⊤) ∨ roundedValue Λ N s ω ∈ A := by
  refine mem_roundedSet.trans ?_
  by_cases h : ∃ i, roundedPoint Λ N s ω i = ⊤
  · obtain ⟨i, hi⟩ := h
    refine iff_of_true ?_ (Or.inl ⟨i, hi⟩)
    rw [boxAbove_eq_empty (ρ := roundedPoint Λ N s ω) hi]
    exact Set.empty_subset _
  · have hne : ∀ i, roundedPoint Λ N s ω i ≠ ⊤ := fun i hi => h ⟨i, hi⟩
    have hbox : boxAbove (roundedPoint Λ N s ω) ⊆ A ↔ roundedValue Λ N s ω ∈ A := by
      rw [roundedPoint_eq_coe Λ N s hne]
      exact boxAbove_subset_iff hA (roundedValue Λ N s ω)
    exact hbox.trans ⟨Or.inr, fun h' => h'.resolve_left h⟩

end Rounded

section Measurability

variable {X : Type*} [MeasurableSpace X] [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
  [BorelSpace X]

/-- The points that round up to `⊤` form a measurable set: they are above every level. -/
theorem measurableSet_roundUp_eq_top (Λ : Finset X) : MeasurableSet {x : X | roundUp Λ x = ⊤} := by
  have h : {x : X | roundUp Λ x = ⊤} = ⋂ d ∈ Λ, Ioi d := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iInter₂.2 fun d hd => Set.mem_Ioi.2 (not_le.1 fun hxd => ?_)
      have hle := roundUp_le hd hxd
      rw [show roundUp Λ x = ⊤ from hx] at hle
      exact WithTop.coe_ne_top (top_le_iff.1 hle)
    · intro hx
      have hx' := Set.mem_iInter₂.1 hx
      show roundUp Λ x = ⊤
      unfold roundUp
      refine Finset.min_eq_top.2 (Finset.eq_empty_of_forall_notMem fun d hd => ?_)
      obtain ⟨hdΛ, hxd⟩ := Finset.mem_filter.1 hd
      exact absurd hxd (not_le.2 (Set.mem_Ioi.1 (hx' d hdΛ)))
  rw [h]
  exact Finset.measurableSet_biInter Λ fun d _ => measurableSet_Ioi

/-- The rounded value, when it is a point of `X` (and `x` itself when it is `⊤`), is a measurable
function of `x`: its preimages are finite unions of measurable sets cut out by the rank. -/
theorem measurable_untopD_roundUp (Λ : Finset X) :
    Measurable fun x : X => (roundUp Λ x).untopD x := by
  have hG : ∀ c : WithTop X, Measurable fun x : X => c.untopD x := by
    intro c
    induction c using WithTop.recTopCoe with
    | top => exact measurable_id
    | coe a => exact measurable_const
  intro S hS
  have key : (fun x : X => (roundUp Λ x).untopD x) ⁻¹' S =
      ⋃ k : Fin (Λ.card + 1),
        rankUp Λ ⁻¹' {k} ∩ (fun x : X => (levelOfRank Λ k).untopD x) ⁻¹' S := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨rankUp Λ x, rfl, by rw [levelOfRank_rankUp]; exact h⟩
    · rintro ⟨k, rfl, h⟩
      rw [levelOfRank_rankUp] at h
      exact h
  rw [key]
  exact MeasurableSet.iUnion fun k =>
    (measurable_rankUp Λ (measurableSet_singleton k)).inter (hG (levelOfRank Λ k) hS)

end Measurability

section RoundedMeasurability

variable {ι : Type*} [DecidableEq ι] {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
  [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, OrderTopology (E i)]
  [∀ i, BorelSpace (E i)]

/-- The set of points whose `i`-th rounded coordinate is `⊤` is measurable. -/
private theorem measurableSet_roundedPoint_eq_top (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ)
    (s : Finset ι) (i : ι) : MeasurableSet {ω : ∀ i, E i | roundedPoint Λ N s ω i = ⊤} := by
  by_cases hi : i ∈ s
  · have h : {ω : ∀ i, E i | roundedPoint Λ N s ω i = ⊤} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun ω hω => ?_
      have h' : roundedPoint Λ N s ω i = ⊤ := hω
      simp only [roundedPoint, hi, ↓reduceIte] at h'
      exact WithTop.coe_ne_top h'
    rw [h]
    exact MeasurableSet.empty
  · have h : {ω : ∀ i, E i | roundedPoint Λ N s ω i = ⊤} =
        (fun ω : ∀ i, E i => ω i) ⁻¹' {x | roundUp (Λ i (N i)) x = ⊤} := by
      ext ω
      simp only [roundedPoint, hi, ↓reduceIte, Set.mem_ofPred_eq, Set.mem_preimage]
    rw [h]
    exact measurable_pi_apply i (measurableSet_roundUp_eq_top _)

/-- The map `ω ↦ roundedValue Λ N s ω` is measurable. -/
private theorem measurable_roundedValue (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ)
    (s : Finset ι) : Measurable (roundedValue Λ N s) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases hi : i ∈ s
  · have h : (fun ω : ∀ i, E i => roundedValue Λ N s ω i) = fun ω => ω i := by
      funext ω
      simp only [roundedValue, hi, ↓reduceIte]
    rw [h]
    exact measurable_pi_apply i
  · have h : (fun ω : ∀ i, E i => roundedValue Λ N s ω i) =
        (fun x => (roundUp (Λ i (N i)) x).untopD x) ∘ fun ω => ω i := by
      funext ω
      simp only [roundedValue, hi, ↓reduceIte, Function.comp_apply]
    rw [h]
    exact (measurable_untopD_roundUp _).comp (measurable_pi_apply i)

/-- For measurable increasing `A`, the set `roundedSet Λ N s A` is measurable. Rounded coordinates
take finitely many values, and finiteness of the index type makes the exceptional set a finite
union. -/
theorem measurableSet_roundedSet [Fintype ι] (Λ : ∀ i, ℕ → Finset (E i)) (N : ι → ℕ)
    (s : Finset ι) {A : Set (∀ i, E i)} (hAm : MeasurableSet A) (hA : IsUpperSet A) :
    MeasurableSet (roundedSet Λ N s A) := by
  have hset : roundedSet Λ N s A =
      (⋃ i, {ω : ∀ i, E i | roundedPoint Λ N s ω i = ⊤}) ∪ roundedValue Λ N s ⁻¹' A := by
    ext ω
    rw [mem_roundedSet_iff Λ N s hA]
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_preimage]
  rw [hset]
  exact (MeasurableSet.iUnion fun i => measurableSet_roundedPoint_eq_top Λ N s i).union
    (measurable_roundedValue Λ N s hAm)

end RoundedMeasurability

end ProbabilityBasics.BK
