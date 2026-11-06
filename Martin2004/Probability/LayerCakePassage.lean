/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Basic
public import LPP_Foundations.Probability.PassageIntegrable
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Layer cake for last-passage differences

This is the layer cake step of the proof of Martin (2004), Lemma 4.2, before the limit in `n`.

For two environments `ω₁`, `ω₂` and a level `x`, the layer environment has, at each site `z`, the
value `I(ω₁ z > x, ω₂ z <= x) - I(ω₁ z <= x, ω₂ z > x)`, written with the half-open intervals
`[ω₂ z, ω₁ z)` and `[ω₁ z, ω₂ z)`. Its integral over `x` is `ω₁ z - ω₂ z`. Hence the
difference of last-passage values is at most the integral over `x` of the last passage of the
layer environment, since the maximum of an integral is at most the integral of the maximum.
With random environments the expectation moves inside the integral over `x` by Fubini's
theorem.

Martin (2004) uses the strict inequality on the other side, `I(X1 >= x, X2 < x)`. The two layer
integrands differ only at the two points `x = X1` and `x = X2`, so every integral over `x` is the
same.
-/

public section

open MeasureTheory Set

namespace LPPDifferentiability

/-- If every coordinate of a random environment is integrable, so is its last-passage value. -/
theorem integrable_lastPassage_of_coord {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → Environment} (hY : ∀ z : Lattice, Integrable (fun ω => Y ω z) P)
    (u : Lattice) (d : ℕ × ℕ) :
    Integrable (fun ω => lastPassage (Y ω) u d) P := by
  classical
  have hp : ∀ p : Path u d, Integrable (fun ω => pathWeight (Y ω) p) P := fun p =>
    integrable_finsetSum Finset.univ fun i _ => hY (p.vertex i.castSucc)
  have hsup : Integrable (Finset.univ.sup' Finset.univ_nonempty
      (fun p : Path u d => fun ω : Ω => pathWeight (Y ω) p)) P :=
    Finset.sup'_induction (p := fun f : Ω → ℝ => Integrable f P) Finset.univ_nonempty _
      (fun _ hf _ hg => hf.sup hg) (fun p _ => hp p)
  have heq : (fun ω => lastPassage (Y ω) u d) = Finset.univ.sup' Finset.univ_nonempty
      (fun p : Path u d => fun ω : Ω => pathWeight (Y ω) p) := by
    funext ω
    simp [lastPassage, Finset.max'_eq_sup', Finset.sup'_image]
  rw [heq]
  exact hsup

/-- The indicator of a bounded half-open interval is integrable on the line. -/
theorem integrable_indicator_Ico (a b : ℝ) :
    Integrable (fun x : ℝ => (Ico a b).indicator (fun _ => (1 : ℝ)) x) := by
  rw [integrable_indicator_iff measurableSet_Ico]
  exact integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top) (by simp)

/-- Layer cake for one site (proof of Martin (2004), Lemma 4.2): the integral over `x` of
`I(a > x, b <= x) - I(a <= x, b > x)` is `a - b`. -/
theorem integral_layerCake_sub (a b : ℝ) :
    ∫ x : ℝ, ((Ico b a).indicator (fun _ => (1 : ℝ)) x -
      (Ico a b).indicator (fun _ => (1 : ℝ)) x) = a - b := by
  have h1 : ∫ x : ℝ, (Ico b a).indicator (fun _ => (1 : ℝ)) x = max (a - b) 0 := by
    rw [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico]
    simp
  have h2 : ∫ x : ℝ, (Ico a b).indicator (fun _ => (1 : ℝ)) x = max (b - a) 0 := by
    rw [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico]
    simp
  rw [integral_sub (integrable_indicator_Ico b a) (integrable_indicator_Ico a b), h1, h2]
  rcases le_total a b with h | h
  · rw [max_eq_right (sub_nonpos.2 h), max_eq_left (sub_nonneg.2 h)]
    ring
  · rw [max_eq_left (sub_nonneg.2 h), max_eq_right (sub_nonpos.2 h)]
    ring

/-- Maximum of an integral is at most the integral of the maximum (proof of Martin (2004),
Lemma 4.2), for last passage: the difference of two last-passage values is at most the integral
over the level `x` of the last passage of the layer environment. -/
theorem lastPassage_sub_le_integral_layer (ω₁ ω₂ : Environment) (d : ℕ × ℕ) :
    lastPassage ω₁ 0 d - lastPassage ω₂ 0 d ≤
      ∫ x : ℝ, lastPassage (fun z : Lattice =>
        (Ico (ω₂ z) (ω₁ z)).indicator (fun _ => (1 : ℝ)) x -
          (Ico (ω₁ z) (ω₂ z)).indicator (fun _ => (1 : ℝ)) x) 0 d := by
  classical
  let L : ℝ → Environment := fun x z =>
    (Ico (ω₂ z) (ω₁ z)).indicator (fun _ => (1 : ℝ)) x -
      (Ico (ω₁ z) (ω₂ z)).indicator (fun _ => (1 : ℝ)) x
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω₁ 0 d
  have hint : ∀ z : Lattice, Integrable (fun x : ℝ => L x z) := fun z =>
    (integrable_indicator_Ico _ _).sub (integrable_indicator_Ico _ _)
  have hLP : Integrable (fun x : ℝ => lastPassage (L x) 0 d) :=
    integrable_lastPassage_of_coord hint 0 d
  have hpw : Integrable (fun x : ℝ => pathWeight (L x) p) :=
    integrable_finsetSum Finset.univ fun i _ => hint (p.vertex i.castSucc)
  have hsum : pathWeight ω₁ p - pathWeight ω₂ p =
      ∑ i : Fin (d.1 + d.2), (ω₁ (p.vertex i.castSucc) - ω₂ (p.vertex i.castSucc)) := by
    unfold pathWeight
    rw [Finset.sum_sub_distrib]
  have hswap : ∫ x : ℝ, pathWeight (L x) p =
      ∑ i : Fin (d.1 + d.2), ∫ x : ℝ, L x (p.vertex i.castSucc) := by
    unfold pathWeight
    exact integral_finsetSum Finset.univ fun i _ => hint (p.vertex i.castSucc)
  calc lastPassage ω₁ 0 d - lastPassage ω₂ 0 d
      ≤ pathWeight ω₁ p - pathWeight ω₂ p := by
        rw [← hp]
        linarith [pathWeight_le_lastPassage ω₂ p]
    _ = ∫ x : ℝ, pathWeight (L x) p := by
        rw [hsum, hswap]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (integral_layerCake_sub (ω₁ (p.vertex i.castSucc))
          (ω₂ (p.vertex i.castSucc))).symm
    _ ≤ ∫ x : ℝ, lastPassage (L x) 0 d :=
        integral_mono hpw hLP fun x => pathWeight_le_lastPassage (L x) p

/-- On the product of a probability space and the line, the indicator that the level `x` lies in
`[b ω, a ω)` is integrable when `a` and `b` are integrable (its integral over `x` is
`(a ω - b ω)_+`). -/
theorem integrable_indicator_Ico_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b)
    (ia : Integrable a P) (ib : Integrable b P) :
    Integrable (fun q : Ω × ℝ => (Ico (b q.1) (a q.1)).indicator (fun _ => (1 : ℝ)) q.2)
      (P.prod volume) := by
  have hmeas : MeasurableSet {q : Ω × ℝ | q.2 ∈ Ico (b q.1) (a q.1)} :=
    (measurableSet_le (hb.comp measurable_fst) measurable_snd).inter
      (measurableSet_lt measurable_snd (ha.comp measurable_fst))
  have hform : (fun q : Ω × ℝ => (Ico (b q.1) (a q.1)).indicator (fun _ => (1 : ℝ)) q.2) =
      {q : Ω × ℝ | q.2 ∈ Ico (b q.1) (a q.1)}.indicator (fun _ => (1 : ℝ)) := by
    funext q
    simp only [indicator_apply, mem_ofPred_eq]
  have hfm : Measurable
      (fun q : Ω × ℝ => (Ico (b q.1) (a q.1)).indicator (fun _ => (1 : ℝ)) q.2) := by
    rw [hform]
    exact measurable_const.indicator hmeas
  have hnorm : ∀ (c e y : ℝ), ‖(Ico c e).indicator (fun _ => (1 : ℝ)) y‖ =
      (Ico c e).indicator (fun _ => (1 : ℝ)) y := by
    intro c e y
    by_cases h : y ∈ Ico c e <;> simp [h]
  have hint : (fun ω => ∫ y : ℝ, ‖(Ico (b ω) (a ω)).indicator (fun _ => (1 : ℝ)) y‖) =
      fun ω => max (a ω - b ω) 0 := by
    funext ω
    simp only [hnorm]
    rw [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico]
    simp
  refine (integrable_prod_iff hfm.aestronglyMeasurable).2
    ⟨Filter.Eventually.of_forall fun ω => integrable_indicator_Ico (b ω) (a ω), ?_⟩
  show Integrable
    (fun ω => ∫ y : ℝ, ‖(Ico (b ω) (a ω)).indicator (fun _ => (1 : ℝ)) y‖) P
  rw [hint]
  exact (ia.sub ib).pos_part

/-- The last passage of the layer environment is integrable on the product of the probability
space and the line. This is the integrability that Fubini's theorem needs (proof of Martin
(2004), Lemma 4.2). -/
theorem integrable_lastPassage_layer_prod
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₁ X₂ : Ω → Environment)
    (hm₁ : ∀ z : Lattice, Measurable fun ω => X₁ ω z)
    (hm₂ : ∀ z : Lattice, Measurable fun ω => X₂ ω z)
    (hi₁ : ∀ z : Lattice, Integrable (fun ω => X₁ ω z) P)
    (hi₂ : ∀ z : Lattice, Integrable (fun ω => X₂ ω z) P) (d : ℕ × ℕ) :
    Integrable (fun q : Ω × ℝ => lastPassage (fun z : Lattice =>
      (Ico (X₂ q.1 z) (X₁ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2 -
        (Ico (X₁ q.1 z) (X₂ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2) 0 d)
      (P.prod volume) := by
  have hlay : ∀ z : Lattice, Integrable (fun q : Ω × ℝ =>
      (Ico (X₂ q.1 z) (X₁ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2 -
        (Ico (X₁ q.1 z) (X₂ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2) (P.prod volume) :=
    fun z =>
      (integrable_indicator_Ico_prod P (fun ω => X₁ ω z) (fun ω => X₂ ω z)
          (hm₁ z) (hm₂ z) (hi₁ z) (hi₂ z)).sub
        (integrable_indicator_Ico_prod P (fun ω => X₂ ω z) (fun ω => X₁ ω z)
          (hm₂ z) (hm₁ z) (hi₂ z) (hi₁ z))
  exact integrable_lastPassage_of_coord
    (Y := fun (q : Ω × ℝ) (z : Lattice) =>
      (Ico (X₂ q.1 z) (X₁ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2 -
        (Ico (X₁ q.1 z) (X₂ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2) hlay 0 d

/-- Fubini step (proof of Martin (2004), Lemma 4.2, without the limit): for random environments with
measurable integrable coordinates, the difference of the mean last-passage values is at most the
integral over the level `x` of the mean last passage of the layer environment. -/
theorem integral_lastPassage_sub_le_integral_layer
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₁ X₂ : Ω → Environment)
    (hm₁ : ∀ z : Lattice, Measurable fun ω => X₁ ω z)
    (hm₂ : ∀ z : Lattice, Measurable fun ω => X₂ ω z)
    (hi₁ : ∀ z : Lattice, Integrable (fun ω => X₁ ω z) P)
    (hi₂ : ∀ z : Lattice, Integrable (fun ω => X₂ ω z) P) (d : ℕ × ℕ) :
    ∫ ω, lastPassage (X₁ ω) 0 d ∂P - ∫ ω, lastPassage (X₂ ω) 0 d ∂P ≤
      ∫ x : ℝ, ∫ ω, lastPassage (fun z : Lattice =>
        (Ico (X₂ ω z) (X₁ ω z)).indicator (fun _ => (1 : ℝ)) x -
          (Ico (X₁ ω z) (X₂ ω z)).indicator (fun _ => (1 : ℝ)) x) 0 d ∂P := by
  classical
  let F : Ω → ℝ → ℝ := fun ω x => lastPassage (fun z : Lattice =>
    (Ico (X₂ ω z) (X₁ ω z)).indicator (fun _ => (1 : ℝ)) x -
      (Ico (X₁ ω z) (X₂ ω z)).indicator (fun _ => (1 : ℝ)) x) 0 d
  have hF : Integrable (Function.uncurry F) (P.prod volume) :=
    integrable_lastPassage_layer_prod P X₁ X₂ hm₁ hm₂ hi₁ hi₂ d
  have hi1 : Integrable (fun ω => lastPassage (X₁ ω) 0 d) P :=
    integrable_lastPassage_of_coord hi₁ 0 d
  have hi2 : Integrable (fun ω => lastPassage (X₂ ω) 0 d) P :=
    integrable_lastPassage_of_coord hi₂ 0 d
  have hmid : Integrable (fun ω => ∫ x : ℝ, F ω x) P := hF.integral_prod_left
  have hpt : ∀ ω, lastPassage (X₁ ω) 0 d - lastPassage (X₂ ω) 0 d ≤ ∫ x : ℝ, F ω x :=
    fun ω => lastPassage_sub_le_integral_layer (X₁ ω) (X₂ ω) d
  calc ∫ ω, lastPassage (X₁ ω) 0 d ∂P - ∫ ω, lastPassage (X₂ ω) 0 d ∂P
      = ∫ ω, (lastPassage (X₁ ω) 0 d - lastPassage (X₂ ω) 0 d) ∂P :=
        (integral_sub hi1 hi2).symm
    _ ≤ ∫ ω, (∫ x : ℝ, F ω x) ∂P :=
        integral_mono (hi1.sub hi2) hmid hpt
    _ = ∫ x : ℝ, ∫ ω, F ω x ∂P := integral_integral_swap hF

end LPPDifferentiability
