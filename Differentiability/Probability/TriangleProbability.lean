/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.OrientedPercolation
public import LPP_Foundations.Probability.FiniteEnvironmentLaw
public import Mathlib.MeasureTheory.Measure.Real
import LPP_Foundations.Probability.EnvironmentLaw
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Triangle events: measurability, exact probability and a floor

A `T`-triangle at `r` (`IsTriangle`) constrains finitely many weights: the `T` sites
above `r`, the site to the right of `r`, and the other sites of a triangle with
`T (T + 1) / 2` sites. This file shows that the triangle event is measurable, that
under the environment law it has the product probability
`ν(Iio 1) ^ T * ν[c₀, 1) * ν{1} ^ (T (T + 1) / 2 - 1)`, and that a floor `c₀ < 1`
with `ν[c₀, 1) > 0` exists when `ν{1} < 1` and `ν` lives on `(-∞, 1]`.

The proof writes the triangle event as "every site of one finite set lies in a
prescribed measurable set", and applies the finite product law of the environment.
-/

public section

open MeasureTheory Set

namespace LPPDifferentiability

/-- The `T` sites directly above `r`. -/
private def triColumn (T : ℕ) (r : Lattice) : Finset Lattice :=
  (Finset.Icc 1 T).image fun i : ℕ => (r.1, r.2 + (i : ℤ))

/-- The sites of the triangle with corner `(r₁ + 1, r₂)`, listed by diagonal. -/
private def triBody (T : ℕ) (r : Lattice) : Finset Lattice :=
  ((Finset.range T).sigma fun k => Finset.antidiagonal k).image
    fun x : (_ : ℕ) × (ℕ × ℕ) => (r.1 + 1 + (x.2.1 : ℤ), r.2 + (x.2.2 : ℤ))

/-- The set that the weight at the site `z` must lie in. -/
private def triPred (c₀ : ℝ) (r : Lattice) (z : Lattice) : Set ℝ :=
  if z.1 = r.1 then Iio 1 else if z = (r.1 + 1, r.2) then Ico c₀ 1 else {1}

private theorem triPred_column (c₀ : ℝ) (r z : Lattice) (h : z.1 = r.1) :
    triPred c₀ r z = Iio 1 := by
  simp [triPred, h]

private theorem triPred_corner (c₀ : ℝ) (r : Lattice) :
    triPred c₀ r (r.1 + 1, r.2) = Ico c₀ 1 := by
  have h : ¬ (r.1 + 1 = r.1) := by omega
  simp [triPred, h]

private theorem triPred_rest (c₀ : ℝ) (r z : Lattice) (h1 : r.1 + 1 ≤ z.1)
    (h : z ≠ (r.1 + 1, r.2)) : triPred c₀ r z = {1} := by
  have h' : z.1 ≠ r.1 := by omega
  simp [triPred, h', h]

private theorem measurableSet_triPred (c₀ : ℝ) (r z : Lattice) :
    MeasurableSet (triPred c₀ r z) := by
  unfold triPred
  split_ifs
  exacts [measurableSet_Iio, measurableSet_Ico, measurableSet_singleton _]

private theorem mem_triColumn (T : ℕ) (r s : Lattice) :
    s ∈ triColumn T r ↔ ∃ i : ℕ, (1 ≤ i ∧ i ≤ T) ∧ (r.1, r.2 + (i : ℤ)) = s := by
  simp only [triColumn, Finset.mem_image, Finset.mem_Icc]

private theorem card_triColumn (T : ℕ) (r : Lattice) : (triColumn T r).card = T := by
  have inj : Function.Injective fun i : ℕ => (r.1, r.2 + (i : ℤ)) := by
    intro i j h
    have h' : r.2 + (i : ℤ) = r.2 + (j : ℤ) := congrArg Prod.snd h
    omega
  rw [triColumn, Finset.card_image_of_injective _ inj, Nat.card_Icc]
  omega

private theorem mem_triBody (T : ℕ) (r z : Lattice) :
    z ∈ triBody T r ↔ r.1 + 1 ≤ z.1 ∧ r.2 ≤ z.2 ∧
      (z.1 - (r.1 + 1)) + (z.2 - r.2) ≤ (T : ℤ) - 1 := by
  simp only [triBody, Finset.mem_image, Finset.mem_sigma, Finset.mem_range,
    Finset.mem_antidiagonal]
  constructor
  · rintro ⟨⟨k, a, b⟩, ⟨hk, hab⟩, rfl⟩
    have hk' : k < T := hk
    have hab' : a + b = k := hab
    refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨(z.1 - (r.1 + 1)).toNat + (z.2 - r.2).toNat,
      ((z.1 - (r.1 + 1)).toNat, (z.2 - r.2).toNat)⟩, ⟨?_, ?_⟩, ?_⟩
    · show (z.1 - (r.1 + 1)).toNat + (z.2 - r.2).toNat < T
      omega
    · show (z.1 - (r.1 + 1)).toNat + (z.2 - r.2).toNat = (z.1 - (r.1 + 1)).toNat +
        (z.2 - r.2).toNat
      rfl
    · exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

private theorem card_triBody (T : ℕ) (r : Lattice) :
    (triBody T r).card = T * (T + 1) / 2 := by
  have inj : Set.InjOn (fun x : (_ : ℕ) × (ℕ × ℕ) => (r.1 + 1 + (x.2.1 : ℤ), r.2 + (x.2.2 : ℤ)))
      ↑((Finset.range T).sigma fun k => Finset.antidiagonal k) := by
    rintro ⟨k, a, b⟩ hx ⟨k', a', b'⟩ hy hxy
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_range,
      Finset.mem_antidiagonal] at hx hy
    have hx' : a + b = k := hx.2
    have hy' : a' + b' = k' := hy.2
    have h1 : r.1 + 1 + (a : ℤ) = r.1 + 1 + (a' : ℤ) := congrArg Prod.fst hxy
    have h2 : r.2 + (b : ℤ) = r.2 + (b' : ℤ) := congrArg Prod.snd hxy
    have ha : a = a' := by omega
    have hb : b = b' := by omega
    have hk : k = k' := by omega
    subst ha hb hk
    rfl
  have key : ∀ n : ℕ, 2 * ∑ k ∈ Finset.range n, (k + 1) = n * (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
  rw [triBody, Finset.card_image_of_injOn inj, Finset.card_sigma]
  simp only [Finset.Nat.card_antidiagonal]
  have := key T
  omega

/-- The finite set of sites constrained by a triangle. -/
private def triSites (T : ℕ) (r : Lattice) : Finset Lattice :=
  triColumn T r ∪ insert (r.1 + 1, r.2) (triBody T r)

private theorem isTriangle_iff_forall (T : ℕ) (c₀ : ℝ) (r : Lattice) (ω : Environment) :
    IsTriangle ω T c₀ r ↔ ∀ s ∈ triSites T r, ω s ∈ triPred c₀ r s := by
  constructor
  · rintro ⟨h1, ⟨h2a, h2b⟩, h3⟩ s hs
    rw [triSites, Finset.mem_union, Finset.mem_insert] at hs
    rcases hs with hs | hs | hs
    · obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := (mem_triColumn T r s).mp hs
      rw [triPred_column c₀ r (r.1, r.2 + (i : ℤ)) rfl]
      exact h1 i hi1 hi2
    · subst hs
      rw [triPred_corner]
      exact ⟨h2a, h2b⟩
    · by_cases hc : s = (r.1 + 1, r.2)
      · subst hc
        rw [triPred_corner]
        exact ⟨h2a, h2b⟩
      · obtain ⟨b1, b2, b3⟩ := (mem_triBody T r s).mp hs
        rw [triPred_rest c₀ r s b1 hc]
        exact h3 s b1 b2 b3 hc
  · intro h
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · intro i hi1 hi2
      have hmem : (r.1, r.2 + (i : ℤ)) ∈ triSites T r :=
        Finset.mem_union_left _ ((mem_triColumn T r _).mpr ⟨i, ⟨hi1, hi2⟩, rfl⟩)
      have := h _ hmem
      rw [triPred_column c₀ r (r.1, r.2 + (i : ℤ)) rfl] at this
      exact this
    · have hmem : ((r.1 + 1, r.2) : Lattice) ∈ triSites T r :=
        Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      have := h _ hmem
      rw [triPred_corner] at this
      exact this.1
    · have hmem : ((r.1 + 1, r.2) : Lattice) ∈ triSites T r :=
        Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      have := h _ hmem
      rw [triPred_corner] at this
      exact this.2
    · intro z h1 h2 h3 hz
      have hmem : z ∈ triSites T r :=
        Finset.mem_union_right _ (Finset.mem_insert_of_mem ((mem_triBody T r z).mpr ⟨h1, h2, h3⟩))
      have := h _ hmem
      rw [triPred_rest c₀ r z h1 hz] at this
      exact this

/-- A finite set of sites lies in prescribed measurable sets with the product probability. -/
private theorem environmentLaw_real_forall_mem (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (A : Finset Lattice) (P : Lattice → Set ℝ) (hP : ∀ z, MeasurableSet (P z)) :
    (environmentLaw ν).real {ω : Environment | ∀ s ∈ A, ω s ∈ P s} =
      ∏ s ∈ A, ν.real (P s) := by
  let coordinates : Environment → A → ℝ := fun ω i => ω i.1
  let rectangle : Set (A → ℝ) := Set.univ.pi (fun i : A => P i.1)
  have hrectangle : MeasurableSet rectangle :=
    MeasurableSet.univ_pi fun i => hP i.1
  have hcoordinates : Measurable coordinates :=
    measurable_finite_environment_coordinates (fun i : A => i.1)
  have hpre : coordinates ⁻¹' rectangle = {ω : Environment | ∀ s ∈ A, ω s ∈ P s} := by
    ext ω
    simp only [coordinates, rectangle, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_ofPred_eq]
    exact ⟨fun h s hs => h ⟨s, hs⟩, fun h i => h i.1 i.2⟩
  have hlaw : (environmentLaw ν).map coordinates = Measure.pi (fun _ : A => ν) :=
    environmentLaw_map_finite_coordinates ν (fun i : A => i.1) Subtype.val_injective
  have hprod : (Measure.pi (fun _ : A => ν)) rectangle = ∏ i : A, ν (P i.1) :=
    Measure.pi_pi (fun _ : A => ν) (fun i : A => P i.1)
  calc
    (environmentLaw ν).real {ω : Environment | ∀ s ∈ A, ω s ∈ P s} =
        (environmentLaw ν).real (coordinates ⁻¹' rectangle) := by rw [hpre]
    _ = ((environmentLaw ν).map coordinates).real rectangle :=
      (map_measureReal_apply hcoordinates hrectangle).symm
    _ = (Measure.pi (fun _ : A => ν)).real rectangle := by rw [hlaw]
    _ = ∏ s ∈ A, ν.real (P s) := by
      rw [measureReal_def, hprod, ENNReal.toReal_prod]
      exact Finset.prod_coe_sort A (fun s => ν.real (P s))

theorem measurableSet_isTriangle (T : ℕ) (c₀ : ℝ) (r : Lattice) :
    MeasurableSet {ω : Environment | IsTriangle ω T c₀ r} := by
  have hset : {ω : Environment | IsTriangle ω T c₀ r} =
      ⋂ s ∈ triSites T r, (fun ω : Environment => ω s) ⁻¹' triPred c₀ r s := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    exact isTriangle_iff_forall T c₀ r ω
  rw [hset]
  exact Finset.measurableSet_biInter _ fun s _ =>
    measurable_environment_eval s (measurableSet_triPred c₀ r s)

theorem triangle_probability (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℕ) (hT : 1 ≤ T)
    (c₀ : ℝ) (r : Lattice) :
    (environmentLaw ν).real {ω | IsTriangle ω T c₀ r} =
      ν.real (Iio 1) ^ T * ν.real (Ico c₀ 1) * ν.real {1} ^ (T * (T + 1) / 2 - 1) := by
  have hc : ((r.1 + 1, r.2) : Lattice) ∈ triBody T r :=
    (mem_triBody T r _).mpr ⟨le_rfl, le_rfl, by omega⟩
  have hset : {ω : Environment | IsTriangle ω T c₀ r} =
      {ω : Environment | ∀ s ∈ triSites T r, ω s ∈ triPred c₀ r s} := by
    ext ω
    exact isTriangle_iff_forall T c₀ r ω
  have hsites : triSites T r = triColumn T r ∪ triBody T r := by
    rw [triSites, Finset.insert_eq_of_mem hc]
  have hdisj : Disjoint (triColumn T r) (triBody T r) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    obtain ⟨i, _, rfl⟩ := (mem_triColumn T r s).mp hs
    have h1 : r.1 + 1 ≤ r.1 := ((mem_triBody T r _).mp hs').1
    omega
  rw [hset, environmentLaw_real_forall_mem ν (triSites T r) (triPred c₀ r)
    (measurableSet_triPred c₀ r), hsites, Finset.prod_union hdisj]
  have hcol : ∏ s ∈ triColumn T r, ν.real (triPred c₀ r s) = ν.real (Iio 1) ^ T := by
    rw [Finset.prod_congr rfl (g := fun _ => ν.real (Iio 1)), Finset.prod_const,
      card_triColumn]
    intro s hs
    obtain ⟨i, _, rfl⟩ := (mem_triColumn T r s).mp hs
    rw [triPred_column c₀ r (r.1, r.2 + (i : ℤ)) rfl]
  have hbody : ∏ s ∈ triBody T r, ν.real (triPred c₀ r s) =
      ν.real (Ico c₀ 1) * ν.real {1} ^ (T * (T + 1) / 2 - 1) := by
    rw [← Finset.mul_prod_erase _ _ hc, triPred_corner]
    congr 1
    rw [Finset.prod_congr rfl (g := fun _ => ν.real {1}), Finset.prod_const,
      Finset.card_erase_of_mem hc, card_triBody]
    intro s hs
    obtain ⟨hne, hs'⟩ := Finset.mem_erase.mp hs
    rw [triPred_rest c₀ r s ((mem_triBody T r s).mp hs').1 hne]
  rw [hcol, hbody, mul_assoc]

theorem exists_triangle_floor (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₁ : ν {1} < 1) (hle : ∀ᵐ t ∂ν, t ≤ 1) :
    ∃ c₀ : ℝ, c₀ < 1 ∧ 0 < ν (Ico c₀ 1) := by
  have hgt : ν (Ioi 1) = 0 := by
    have h : ν {a : ℝ | ¬ a ≤ 1} = 0 := ae_iff.mp hle
    have e : {a : ℝ | ¬ a ≤ 1} = Ioi 1 := by
      ext a
      simp
    rwa [e] at h
  have hIio : 0 < ν (Iio 1) := by
    by_contra h
    have h0 : ν (Iio 1) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp h)
    have hcover : (Set.univ : Set ℝ) ⊆ Iio 1 ∪ {1} ∪ Ioi 1 := by
      intro a _
      rcases lt_trichotomy a 1 with h' | h' | h' <;> simp [h']
    have h1 : (1 : ENNReal) ≤ ν (Iio 1) + ν {1} + ν (Ioi 1) :=
      calc (1 : ENNReal) = ν Set.univ := measure_univ.symm
        _ ≤ ν (Iio 1 ∪ {1} ∪ Ioi 1) := measure_mono hcover
        _ ≤ ν (Iio 1 ∪ {1}) + ν (Ioi 1) := measure_union_le _ _
        _ ≤ ν (Iio 1) + ν {1} + ν (Ioi 1) := by
          gcongr
          exact measure_union_le _ _
    rw [h0, hgt, zero_add, add_zero] at h1
    exact absurd h1 (not_le.mpr hp₁)
  have hU : Iio (1 : ℝ) = ⋃ n : ℕ, Ico (-(n : ℝ)) 1 := by
    ext a
    simp only [mem_Iio, mem_iUnion, mem_Ico]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_ge (-a)
      exact ⟨n, by linarith, h⟩
    · rintro ⟨n, _, h⟩
      exact h
  by_contra hne
  push Not at hne
  have hzero : ν (Iio 1) = 0 := by
    rw [hU]
    refine measure_iUnion_null fun n => nonpos_iff_eq_zero.mp (hne (-(n : ℝ)) ?_)
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  exact absurd hzero hIio.ne'

end LPPDifferentiability
