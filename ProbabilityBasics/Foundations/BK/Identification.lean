/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Order.UpperLower.Basic

/-!
# Identification of coordinates

This module holds the set-level identifications used in Theorem 1.6 of van den Berg and
Kesten (1985), for the coordinate set `R = ℕ`.

* `pairImage i j A` is the image of `A` under `(i, j)`-identification (p. 557).
* `identImage rep A` is the image of `A` under identification according to a
  partition with chosen representatives (p. 557). The partition is encoded by
  a map `rep` with `rep (rep j) = rep j` (`IsRepresentativeMap`): the classes are
  the fibres of `rep` and the representatives are its fixed points.
* `identImage_eq_pairImage` is the bookkeeping identity behind the proof of
  Theorem 1.6 (i) ("apply Lemma 1.3 successively"): removing one
  non-representative `j` from its class gives an `(rep j, j)`-image.
* `identImage_sum_elim` and `identImage_sum_iUnion_prod` are the computation of
  the image for the partition into the classes `{k, m + k}` in the proof of
  Theorem 1.6 (ii) (p. 559), for the index type `α ⊕ α`.

Measures do not appear here; the probability statements are in later modules.

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985), Lemma 1.3 and Theorem 1.6.
-/

@[expose] public section

open scoped Pointwise

namespace ProbabilityBasics.BK

variable {ι : Type*}

/-- Image of `A` under `(i, j)`-identification (van den Berg and Kesten 1985,
p. 557, before (1.2)): the points `x` with some `a ∈ A` such that
`x i ≥ a i + a j` and `x k ≥ a k` for every `k ≠ i, j`. -/
def pairImage (i j : ι) (A : Set (ι → ℕ)) : Set (ι → ℕ) :=
  {x | ∃ a ∈ A, a i + a j ≤ x i ∧ ∀ k, k ≠ i → k ≠ j → a k ≤ x k}

/-- A choice of partition and representatives, encoded by a map: `rep j` is the
representative of the class of `j`. The condition `rep (rep j) = rep j` says that
a representative represents itself. This encodes exactly the pairs
(partition, representatives). -/
def IsRepresentativeMap (rep : ι → ι) : Prop :=
  ∀ j, rep (rep j) = rep j

/-! ### Images are increasing -/

/-- The `(i, j)`-image of any set is increasing (used when Lemma 1.3 is applied
to an image, as in the proof of Theorem 1.6 (i), p. 558). -/
theorem isUpperSet_pairImage (i j : ι) (A : Set (ι → ℕ)) :
    IsUpperSet (pairImage i j A) := by
  intro x y hxy hx
  obtain ⟨a, ha, hij, hk⟩ := hx
  exact ⟨a, ha, hij.trans (hxy i), fun k hki hkj => (hk k hki hkj).trans (hxy k)⟩

variable [Fintype ι] [DecidableEq ι]

/-- Image of `A` under identification according to the partition whose classes
are the fibres of `rep`, with the fixed points of `rep` as representatives
(van den Berg and Kesten 1985, p. 557, after (1.2)): the points `x` such that
some `a ∈ A` has `x r ≥ ∑_{j in the class of r} a j` for every representative `r`.
There is no condition on `x j` when `j` is not a representative. -/
def identImage (rep : ι → ι) (A : Set (ι → ℕ)) : Set (ι → ℕ) :=
  {x | ∃ a ∈ A, ∀ r, rep r = r → (∑ j with rep j = r, a j) ≤ x r}

/-- The image under identification according to a partition is increasing
(p. 557). -/
theorem isUpperSet_identImage (rep : ι → ι) (A : Set (ι → ℕ)) :
    IsUpperSet (identImage rep A) := by
  intro x y hxy hx
  obtain ⟨a, ha, h⟩ := hx
  exact ⟨a, ha, fun r hr => (h r hr).trans (hxy r)⟩

/-! ### The trivial partition and the one-step identity -/

/-- The class of `r` for the trivial partition is `{r}`. -/
private theorem sum_fibre_id (a : ι → ℕ) (r : ι) : (∑ j with id j = r, a j) = a r := by
  have hset : Finset.univ.filter (fun j : ι => id j = r) = {r} := by
    ext j
    simp
  rw [hset, Finset.sum_singleton]

/-- With every class a single point, identification does nothing to an
increasing set. This is the base of the successive application of Lemma 1.3 in
the proof of Theorem 1.6 (i) (p. 558). -/
theorem identImage_id {A : Set (ι → ℕ)} (hA : IsUpperSet A) : identImage id A = A := by
  ext x
  constructor
  · rintro ⟨a, ha, h⟩
    refine hA (fun r => ?_) ha
    have hr := h r rfl
    rwa [sum_fibre_id] at hr
  · intro hx
    exact ⟨x, hx, fun r _ => (sum_fibre_id x r).le⟩

section OneStep

variable {rep : ι → ι} {j : ι}

/-- Sum of `a` over the class of `r`. -/
private abbrev classSum (rep : ι → ι) (a : ι → ℕ) (r : ι) : ℕ :=
  ∑ k with rep k = r, a k

/-- Classes of other representatives are unchanged when `j` becomes a singleton
class. -/
private theorem classSum_update_of_ne (a : ι → ℕ) {r : ι}
    (hrj : r ≠ j) (hri : r ≠ rep j) :
    classSum (Function.update rep j j) a r = classSum rep a r := by
  unfold classSum
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  by_cases hk : k = j
  · subst hk
    simp [hrj.symm, hri.symm]
  · simp [Function.update_of_ne hk]

/-- The class of `rep j` loses exactly the point `j`: the sum split
`∑_{rep = i} a = ∑_{rep' = i} a + a j`. -/
private theorem classSum_split (hj : rep j ≠ j) (a : ι → ℕ) :
    classSum rep a (rep j) =
      classSum (Function.update rep j j) a (rep j) + a j := by
  unfold classSum
  have hjnot : j ∉ Finset.univ.filter fun k => Function.update rep j j k = rep j := by
    simp [hj.symm]
  have hset : Finset.univ.filter (fun k => rep k = rep j) =
      insert j (Finset.univ.filter fun k => Function.update rep j j k = rep j) := by
    ext k
    by_cases hk : k = j
    · subst hk
      simp
    · simp [hk]
  rw [hset, Finset.sum_insert hjnot, add_comm]

/-- After the update, the class of `j` is `{j}`. -/
private theorem classSum_update_self (hrep : IsRepresentativeMap rep) (hj : rep j ≠ j)
    (a : ι → ℕ) : classSum (Function.update rep j j) a j = a j := by
  unfold classSum
  have hset : Finset.univ.filter (fun k => Function.update rep j j k = j) = {j} := by
    ext k
    by_cases hk : k = j
    · subst hk
      simp
    · simp only [Function.update_of_ne hk, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, hk, iff_false]
      intro hkj
      exact hj (by rw [← hkj, hrep k, hkj])
  rw [hset, Finset.sum_singleton]

/-- **Bookkeeping for Theorem 1.6 (i)** (p. 558): the image of `A` under
identification according to `rep` is the `(rep j, j)`-image of the image under
identification according to `rep` with `j` made a singleton class. The paper
does not write this identity; it says the identification is obtained by applying
Lemma 1.3 successively to the pairs `(i_F, j)` with `j ≠ i_F`. -/
theorem identImage_eq_pairImage (hrep : IsRepresentativeMap rep) (hj : rep j ≠ j)
    (A : Set (ι → ℕ)) :
    identImage rep A = pairImage (rep j) j (identImage (Function.update rep j j) A) := by
  have hrepj : rep (rep j) = rep j := hrep j
  have hij : rep j ≠ j := hj
  ext x
  constructor
  · -- Forward direction: build the intermediate point `y` of the image for `rep'`.
    rintro ⟨a, ha, hx⟩
    let y : ι → ℕ := fun k =>
      if k = rep j then classSum (Function.update rep j j) a (rep j)
      else if k = j then a j else x k
    have hyi : y (rep j) = classSum (Function.update rep j j) a (rep j) := by simp [y]
    have hyj : y j = a j := by simp [y, hij.symm]
    have hyk : ∀ k, k ≠ rep j → k ≠ j → y k = x k := by
      intro k hki hkj
      simp [y, hki, hkj]
    refine ⟨y, ⟨a, ha, ?_⟩, ?_, fun k hki hkj => (hyk k hki hkj).le⟩
    · intro r hr
      show classSum (Function.update rep j j) a r ≤ y r
      by_cases hrj : r = j
      · rw [hrj]
        exact (classSum_update_self hrep hj a).le.trans hyj.ge
      · have hfix : rep r = r := by simpa [Function.update_of_ne hrj] using hr
        by_cases hri : r = rep j
        · rw [hri]
          exact hyi.ge
        · have hxr : classSum rep a r ≤ x r := hx r hfix
          calc classSum (Function.update rep j j) a r = classSum rep a r :=
                classSum_update_of_ne a hrj hri
            _ ≤ x r := hxr
            _ = y r := (hyk r hri hrj).symm
    · rw [hyi, hyj, ← classSum_split hj a]
      exact hx (rep j) hrepj
  · -- Reverse direction: the same witness `a` works.
    rintro ⟨y, ⟨a, ha, hy⟩, hyij, hyk⟩
    refine ⟨a, ha, fun r hr => ?_⟩
    show classSum rep a r ≤ x r
    by_cases hri : r = rep j
    · rw [hri]
      have h1 : classSum (Function.update rep j j) a (rep j) ≤ y (rep j) :=
        hy (rep j) (by rw [Function.update_of_ne hij, hrepj])
      have h2 : a j ≤ y j :=
        (classSum_update_self hrep hj a).symm.le.trans (hy j (by simp))
      calc classSum rep a (rep j)
          = classSum (Function.update rep j j) a (rep j) + a j := classSum_split hj a
        _ ≤ y (rep j) + y j := Nat.add_le_add h1 h2
        _ ≤ x (rep j) := hyij
    · have hrj : r ≠ j := by
        rintro rfl
        exact hj hr
      have hfix : Function.update rep j j r = r := by
        simpa [Function.update_of_ne hrj] using hr
      calc classSum rep a r
          = classSum (Function.update rep j j) a r :=
            (classSum_update_of_ne a hrj hri).symm
        _ ≤ y r := hy r hfix
        _ ≤ x r := hyk r hri hrj

end OneStep

/-! ### Sums of pairs, and the partition `{k, m + k}` of Theorem 1.6 (ii) -/

/-- `sumUpper D` is the set of `z` lying above `a + b` for some `(a, b) ∈ D`. For
`D = ⋃ (A_l × B_l)` it is the set `⋃ (A_l + B_l)` of (1.8) when the `B_l`
are increasing (`sumUpper_iUnion_prod`). -/
def sumUpper {α : Type*} (D : Set ((α → ℕ) × (α → ℕ))) : Set (α → ℕ) :=
  {z | ∃ p ∈ D, p.1 + p.2 ≤ z}

/-- `sumUpper D` is increasing for every `D`. -/
theorem isUpperSet_sumUpper {α : Type*} (D : Set ((α → ℕ) × (α → ℕ))) :
    IsUpperSet (sumUpper D) := by
  rintro z z' hzz ⟨p, hp, h⟩
  exact ⟨p, hp, h.trans hzz⟩

/-- `sumUpper` commutes with unions. -/
theorem sumUpper_iUnion {α κ : Type*} (D : κ → Set ((α → ℕ) × (α → ℕ))) :
    sumUpper (⋃ l, D l) = ⋃ l, sumUpper (D l) := by
  ext z
  constructor
  · rintro ⟨p, hp, h⟩
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hp
    exact Set.mem_iUnion.mpr ⟨l, p, hl, h⟩
  · intro hz
    obtain ⟨l, p, hl, h⟩ := Set.mem_iUnion.mp hz
    exact ⟨p, Set.mem_iUnion.mpr ⟨l, hl⟩, h⟩

/-- For increasing `B`, `sumUpper (A ×ˢ B) = A + B`: a point above `a + b` is
`a + b'` with `b' = z - a` above `b`, hence in `B` (proof of (1.8), p. 559,
"as is easily seen"). The paper has both sets increasing; only `B` is used. -/
theorem sumUpper_prod {α : Type*} {A B : Set (α → ℕ)} (hB : IsUpperSet B) :
    sumUpper (A ×ˢ B) = A + B := by
  ext z
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, h⟩
    have hab : ∀ k, a k + b k ≤ z k := fun k => h k
    refine Set.mem_add.mpr ⟨a, ha, z - a, hB (fun k => ?_) hb, ?_⟩
    · have hk := hab k
      show b k ≤ z k - a k
      omega
    · funext k
      have hk := hab k
      show a k + (z k - a k) = z k
      omega
  · intro hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hz
    exact ⟨(a, b), ⟨ha, hb⟩, le_rfl⟩

/-- The same for a union over any index type: the set `⋃ (A_l + B_l)` of (1.8),
p. 558, with increasing `B_l` (the paper also has `A_l` increasing; not needed here). -/
theorem sumUpper_iUnion_prod {α κ : Type*} {A B : κ → Set (α → ℕ)}
    (hB : ∀ l, IsUpperSet (B l)) :
    sumUpper (⋃ l, A l ×ˢ B l) = ⋃ l, A l + B l := by
  rw [sumUpper_iUnion]
  exact congrArg Set.iUnion (funext fun l => sumUpper_prod (hB l))

section SumIndex

variable {α : Type*}

/-- The partition of `α ⊕ α` into the classes `{inl k, inr k}` with
representatives `inl k` (proof of Theorem 1.6 (ii), p. 558, with `α = {1..m}`)
is a representative map. -/
theorem isRepresentativeMap_sumElim :
    IsRepresentativeMap (Sum.elim Sum.inl Sum.inl : α ⊕ α → α ⊕ α) := by
  intro j
  cases j <;> rfl

variable [Fintype α] [DecidableEq α]

/-- The class sum for the partition `{inl k, inr k}`. -/
private theorem sum_class_inl (a : α ⊕ α → ℕ) (k : α) :
    (∑ j with (Sum.elim Sum.inl Sum.inl : α ⊕ α → α ⊕ α) j = Sum.inl k, a j) =
      a (Sum.inl k) + a (Sum.inr k) := by
  have hset : Finset.univ.filter
      (fun j : α ⊕ α => (Sum.elim Sum.inl Sum.inl : α ⊕ α → α ⊕ α) j = Sum.inl k) =
      {Sum.inl k, Sum.inr k} := by
    ext j
    cases j <;> simp
  rw [hset, Finset.sum_pair (by simp)]

/-- **Image for the partition `{k, m + k}`** (Theorem 1.6 (ii), p. 559). An
increasing set `D` of pairs `(a, b)` of points of `ℕ^α` is viewed as a set of
points `z` of `ℕ^(α ⊕ α)` through `z ↦ (z ∘ inl, z ∘ inr)` (the underlying map
of `MeasurableEquiv.sumPiEquivProdPi`). Its image under identification with
representatives `inl k` is `{x | x ∘ inl ∈ sumUpper D}`: the last `m`
coordinates are free. -/
theorem identImage_sum_elim (D : Set ((α → ℕ) × (α → ℕ))) :
    identImage (Sum.elim Sum.inl Sum.inl : α ⊕ α → α ⊕ α)
        ((fun z : α ⊕ α → ℕ => (z ∘ Sum.inl, z ∘ Sum.inr)) ⁻¹' D) =
      (fun x : α ⊕ α → ℕ => x ∘ Sum.inl) ⁻¹' sumUpper D := by
  ext x
  constructor
  · rintro ⟨z, hz, h⟩
    refine ⟨(z ∘ Sum.inl, z ∘ Sum.inr), hz, fun k => ?_⟩
    have := h (Sum.inl k) rfl
    rwa [sum_class_inl] at this
  · rintro ⟨⟨a, b⟩, hab, h⟩
    refine ⟨Sum.elim a b, hab, fun r hr => ?_⟩
    cases r with
    | inl k =>
      rw [sum_class_inl]
      exact h k
    | inr k => cases hr

/-- **The set `A*` of Theorem 1.6 (ii)** (p. 559): for increasing `B_l` (and any `A_l`)
and `D = ⋃ (A_l × B_l)`, the image is `(⋃ (A_l + B_l)) × ℕ^α`, written as the
preimage under `x ↦ x ∘ inl`. -/
theorem identImage_sum_iUnion_prod {κ : Type*} {A B : κ → Set (α → ℕ)}
    (hB : ∀ l, IsUpperSet (B l)) :
    identImage (Sum.elim Sum.inl Sum.inl : α ⊕ α → α ⊕ α)
        ((fun z : α ⊕ α → ℕ => (z ∘ Sum.inl, z ∘ Sum.inr)) ⁻¹' ⋃ l, A l ×ˢ B l) =
      (fun x : α ⊕ α → ℕ => x ∘ Sum.inl) ⁻¹' ⋃ l, A l + B l := by
  rw [identImage_sum_elim, sumUpper_iUnion_prod hB]

end SumIndex

end ProbabilityBasics.BK
