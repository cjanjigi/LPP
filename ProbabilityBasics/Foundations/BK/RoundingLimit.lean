/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Foundations.BK.Rounding
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Measure.Continuity

/-!
# The one-coordinate rounding limit

This step helps extend the BK inequality of van den Berg and Kesten (1985), Theorem 3.3, from
finite Bernoulli products to finite products of ordered spaces. It removes the rounding of one
coordinate without changing the measure in the limit.

Fix a coordinate `k`, finite sets of levels `Λ m` in `E k` that increase with `m`, and a level set
`D` of the law `μ k` (`IsLevelSet`) with `⋃ m, Λ m = D`. Let `A` be a measurable increasing set of
`∀ i, E i` and `R m = roundCoord k (Λ m) A`.

* `subset_roundCoord`, `roundCoord_anti`, `measurableSet_roundCoord` (part (a)): `A ⊆ R m`,
  the `R m` decrease as the level set grows, and each `R m` is measurable.
* `measure_iInter_roundCoord_diff` (part (b)): `(⋂ m, R m) \ A` is null for the product law.
  Fixing all coordinates but `k`, the section of this set has at most one point, which is neither a
  level nor an atom; Fubini (Mathlib's marginal integrals) finishes.
* `tendsto_measure_roundCoord` (part (c)): `P (R m)` tends to `P A`, by continuity from above.

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985).
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityBasics.BK

section Monotonicity

variable {ι : Type*} [DecidableEq ι] {E : ι → Type*} [∀ i, LinearOrder (E i)]

/-- Raising coordinate `k` raises the point (a helper for the lemmas below). -/
private theorem update_le_update {k : ι} (ω : ∀ i, E i) {a b : E k} (h : a ≤ b) :
    Function.update ω k a ≤ Function.update ω k b := fun i => by
  rcases eq_or_ne i k with rfl | hik
  · rw [Function.update_self, Function.update_self]
    exact h
  · rw [Function.update_of_ne hik, Function.update_of_ne hik]

/-- For increasing `A`, the set `A` lies inside every `roundCoord k Λk A`: a move of coordinate `k`
to a value at or above the rounded value is an upward move. -/
theorem subset_roundCoord (k : ι) (Λk : Finset (E k)) {A : Set (∀ i, E i)} (hA : IsUpperSet A) :
    A ⊆ roundCoord k Λk A := by
  intro ω hω x hx
  have hωx : ω k ≤ x := WithTop.coe_le_coe.1 ((le_roundUp Λk (ω k)).trans hx)
  have hle : ω ≤ Function.update ω k x := by
    have h := update_le_update ω hωx
    rwa [Function.update_eq_self] at h
  exact hA hle hω

/-- Adding levels shrinks `roundCoord`: the rounded value is lower, so more upper moves are
required. -/
theorem roundCoord_anti (k : ι) {Λk Λk' : Finset (E k)} (h : Λk ⊆ Λk') (A : Set (∀ i, E i)) :
    roundCoord k Λk' A ⊆ roundCoord k Λk A :=
  fun _ hω x hx => hω x ((roundUp_anti h _).trans hx)

/-- For increasing `A`, `roundCoord k Λk A` is the set where coordinate `k` rounds to `⊤` together
with the preimage of `A` under the map that replaces coordinate `k` by its rounded value. If the
rounded value is a point `c`, "all `x ≥ c`" is the same as `x = c`. -/
private theorem roundCoord_eq_union (k : ι) (Λk : Finset (E k)) {A : Set (∀ i, E i)}
    (hA : IsUpperSet A) :
    roundCoord k Λk A = {ω | roundUp Λk (ω k) = ⊤} ∪
      {ω | Function.update ω k ((roundUp Λk (ω k)).untopD (ω k)) ∈ A} := by
  ext ω
  by_cases htop : roundUp Λk (ω k) = ⊤
  · refine iff_of_true (fun x hx => ?_) (Or.inl htop)
    rw [htop] at hx
    exact absurd (top_le_iff.1 hx) WithTop.coe_ne_top
  · obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 htop
    have hu : (roundUp Λk (ω k)).untopD (ω k) = c := by rw [← hc, WithTop.untopD_coe]
    simp only [Set.mem_union, Set.mem_ofPred_eq, htop, false_or, hu]
    constructor
    · exact fun h => h c hc.ge
    · intro h x hx
      rw [← hc, WithTop.coe_le_coe] at hx
      exact hA (update_le_update ω hx) h

end Monotonicity

section Measurability

variable {ι : Type*} [DecidableEq ι] {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
  [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, OrderTopology (E i)]
  [∀ i, BorelSpace (E i)]

/-- The map that replaces coordinate `k` by its rounded value (and leaves the point alone when the
rounded value is `⊤`) is measurable. -/
private theorem measurable_updateRounded (k : ι) (Λk : Finset (E k)) :
    Measurable fun ω : ∀ i, E i => Function.update ω k ((roundUp Λk (ω k)).untopD (ω k)) := by
  refine measurable_pi_iff.2 fun i => ?_
  rcases eq_or_ne i k with rfl | hik
  · simp only [Function.update_self]
    exact (measurable_untopD_roundUp Λk).comp (measurable_pi_apply i)
  · simp only [Function.update_of_ne hik]
    exact measurable_pi_apply i

/-- For measurable increasing `A`, every `roundCoord k Λk A` is measurable. This is
the general case, not only sets of the form `roundedSet ..`. -/
theorem measurableSet_roundCoord (k : ι) (Λk : Finset (E k)) {A : Set (∀ i, E i)}
    (hAm : MeasurableSet A) (hA : IsUpperSet A) : MeasurableSet (roundCoord k Λk A) := by
  rw [roundCoord_eq_union k Λk hA]
  exact (measurable_pi_apply k (measurableSet_roundUp_eq_top Λk)).union
    (measurable_updateRounded k Λk hAm)

end Measurability

section Limit

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
  [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, OrderTopology (E i)]
  [∀ i, BorelSpace (E i)]

/-- The exceptional set `(⋂ m, roundCoord k (Λ m) A) \ A` has product measure zero.
Fix the other coordinates. Its section along `k` has at most one point, because two such points
`t < t'` would be separated by a level `d ∈ Λ m`, which makes `t'` lie in `A`. That point is not a
level, since every level `t ∈ Λ m` rounds to itself; so it is not an atom. Fubini then gives
measure zero. -/
theorem measure_iInter_roundCoord_diff (μ : ∀ i, Measure (E i)) [∀ i, SigmaFinite (μ i)] (k : ι)
    (Λ : ℕ → Finset (E k)) {D : Set (E k)} (hD : IsLevelSet (μ k) D)
    (hΛD : ⋃ m, ((Λ m : Finset (E k)) : Set (E k)) = D) {A : Set (∀ i, E i)}
    (hAm : MeasurableSet A) (hA : IsUpperSet A) :
    Measure.pi μ ((⋂ m, roundCoord k (Λ m) A) \ A) = 0 := by
  set Z : Set (∀ i, E i) := (⋂ m, roundCoord k (Λ m) A) \ A with hZdef
  have hZ : MeasurableSet Z :=
    (MeasurableSet.iInter fun m => measurableSet_roundCoord k (Λ m) hAm hA).diff hAm
  -- every level of `D` lies in some `Λ m`
  have hlevel : ∀ d ∈ D, ∃ m, d ∈ Λ m := fun d hd => by
    have hd' : d ∈ ⋃ m, ((Λ m : Finset (E k)) : Set (E k)) := by rw [hΛD]; exact hd
    simpa only [Set.mem_iUnion, Finset.mem_coe] using hd'
  -- a point of the section is not a level
  have hnotlevel : ∀ (x : ∀ i, E i) (t : E k), Function.update x k t ∈ Z → t ∉ D := by
    intro x t ht htD
    obtain ⟨m, hm⟩ := hlevel t htD
    have hR : Function.update x k t ∈ roundCoord k (Λ m) A := Set.mem_iInter.1 ht.1 m
    have hmem := mem_roundCoord.1 hR t (by
      rw [Function.update_self]
      exact roundUp_le hm le_rfl)
    rw [Function.update_idem] at hmem
    exact ht.2 hmem
  -- the section has at most one point
  have hone : ∀ (x : ∀ i, E i) (t t' : E k), t < t' → Function.update x k t ∈ Z →
      Function.update x k t' ∈ Z → False := by
    intro x t t' htt' ht ht'
    obtain ⟨d, hdD, htd, hdt'⟩ := hD.between t t' htt'
    obtain ⟨m, hm⟩ := hlevel d hdD
    have hR : Function.update x k t ∈ roundCoord k (Λ m) A := Set.mem_iInter.1 ht.1 m
    have hmem := mem_roundCoord.1 hR t' (by
      rw [Function.update_self]
      exact (roundUp_le hm htd.le).trans (WithTop.coe_le_coe.2 hdt'))
    rw [Function.update_idem] at hmem
    exact ht'.2 hmem
  -- the section is null
  have hsection : ∀ x : ∀ i, E i, μ k {t | Function.update x k t ∈ Z} = 0 := by
    intro x
    by_cases hne : ∃ t₀, Function.update x k t₀ ∈ Z
    · obtain ⟨t₀, ht₀⟩ := hne
      have hsub : {t | Function.update x k t ∈ Z} ⊆ {t₀} := fun t ht => by
        rcases lt_trichotomy t t₀ with h | h | h
        · exact (hone x t t₀ h ht ht₀).elim
        · exact h
        · exact (hone x t₀ t h ht₀ ht).elim
      have hnot : ¬ 0 < μ k {t₀} := fun h => hnotlevel x t₀ ht₀ (hD.atoms t₀ h)
      exact measure_mono_null hsub (nonpos_iff_eq_zero.1 (not_lt.1 hnot))
    · have hempty : {t | Function.update x k t ∈ Z} = ∅ :=
        Set.eq_empty_of_forall_notMem fun t ht => hne ⟨t, ht⟩
      rw [hempty, measure_empty]
  -- Fubini, through the marginal integral over the single coordinate `k`
  have hfm : Measurable (Z.indicator (1 : (∀ i, E i) → ENNReal)) := measurable_one.indicator hZ
  calc Measure.pi μ Z = ∫⁻ ω, Z.indicator (1 : (∀ i, E i) → ENNReal) ω ∂Measure.pi μ :=
        (lintegral_indicator_one hZ).symm
    _ = ∫⁻ ω, (0 : (∀ i, E i) → ENNReal) ω ∂Measure.pi μ := by
        refine lintegral_eq_of_lmarginal_eq {k} hfm measurable_zero ?_
        rw [lmarginal_singleton, lmarginal_singleton]
        funext x
        refine lintegral_congr_ae ?_
        rw [Filter.EventuallyEq, ae_iff]
        refine measure_mono_null (fun t ht => ?_) (hsection x)
        by_contra hz
        have hz' : Function.update x k t ∉ Z := hz
        exact ht (by simp only [Set.indicator_of_notMem hz', Pi.zero_apply])
    _ = 0 := by simp

/-- The measures of `roundCoord k (Λ m) A` tend to the measure of `A`: the sets
decrease, are measurable, and their intersection differs from `A` by a null set. -/
theorem tendsto_measure_roundCoord (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (k : ι) (Λ : ℕ → Finset (E k)) (hΛ : Monotone Λ) {D : Set (E k)} (hD : IsLevelSet (μ k) D)
    (hΛD : ⋃ m, ((Λ m : Finset (E k)) : Set (E k)) = D) {A : Set (∀ i, E i)}
    (hAm : MeasurableSet A) (hA : IsUpperSet A) :
    Filter.Tendsto (fun m => Measure.pi μ (roundCoord k (Λ m) A)) Filter.atTop
      (nhds (Measure.pi μ A)) := by
  have hanti : Antitone fun m => roundCoord k (Λ m) A := fun _ _ h =>
    roundCoord_anti k (hΛ h) A
  have hlim := tendsto_measure_iInter_atTop (μ := Measure.pi μ)
    (fun m => (measurableSet_roundCoord k (Λ m) hAm hA).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have hnull := measure_iInter_roundCoord_diff μ k Λ hD hΛD hAm hA
  have heq : Measure.pi μ (⋂ m, roundCoord k (Λ m) A) = Measure.pi μ A := by
    refine le_antisymm ?_ (measure_mono fun ω hω => Set.mem_iInter.2 fun m =>
      subset_roundCoord k (Λ m) hA hω)
    calc Measure.pi μ (⋂ m, roundCoord k (Λ m) A)
        ≤ Measure.pi μ (A ∪ ((⋂ m, roundCoord k (Λ m) A) \ A)) :=
          measure_mono fun ω hω => by
            by_cases hωA : ω ∈ A
            · exact Or.inl hωA
            · exact Or.inr ⟨hω, hωA⟩
      _ ≤ Measure.pi μ A + Measure.pi μ ((⋂ m, roundCoord k (Λ m) A) \ A) := measure_union_le _ _
      _ = Measure.pi μ A := by rw [hnull, add_zero]
  rw [heq] at hlim
  exact hlim

end Limit

end ProbabilityBasics.BK
