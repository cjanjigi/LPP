/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.GridCrossingTrials
public import Differentiability.Probability.HeavyVertexEvents
public import LPP_Foundations.Probability.DisjointSupportEvents
import Mathlib.Tactic

/-!
# Independence and the all-fail bound for heavy-trimmed crossing trials

At a coarse scale, each crossing trial `E ν` is intersected with the event `H ν` that no site
of its block has weight above `w`. The trials `E ν` come from `coarse_crossing_trials`; the
heavy-vertex events are the no-heavy-site events of the same blocks.

* `heavy_crossing_trials_indep`: the intersections `E ν ∩ H ν` are independent over `ν`;
  each has probability at least `q0 / 2` when `P(E0) > q0` and the heavy-vertex
  failure probability of each block is at most `q0 / 2`; and the probability that all of them
  fail is at most `exp (-(q0 / 2) N)`.

The smallness hypothesis is the probability part of the heavy-vertices lemma, which is
proved in `heavy_coarse_block_events_eventually`. It is not proved again here.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- The event that no site of the finite set `S` has weight above `t` is measurable. -/
private theorem measurableSet_no_heavy (S : Finset Lattice) (t : ℝ) :
    MeasurableSet {ω : Environment | ∀ z ∈ S, ω z ≤ t} := by
  have hset : {ω : Environment | ∀ z ∈ S, ω z ≤ t} =
      ⋂ z ∈ S, {ω : Environment | ω z ≤ t} := by
    ext ω
    simp
  rw [hset]
  exact Finset.measurableSet_biInter S fun z _ =>
    measurableSet_le (measurable_pi_apply z) measurable_const

/-- The no-heavy-site event of `S` depends only on the weights on `S`. -/
private theorem no_heavy_local (S : Finset Lattice) (t : ℝ) (η η' : Environment)
    (hag : ∀ z ∈ S, η z = η' z) :
    η ∈ {ω : Environment | ∀ z ∈ S, ω z ≤ t} ↔
      η' ∈ {ω : Environment | ∀ z ∈ S, ω z ≤ t} := by
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hη z hz
    rw [← hag z hz]
    exact hη z hz
  · intro hη z hz
    rw [hag z hz]
    exact hη z hz

/-- **Independence and all-fail bound for heavy-trimmed crossing trials.**
Let `E ν` be the crossing trials of one coarse grid interval, as in `coarse_crossing_trials`,
with blocks `B ν` (membership as in that theorem) of threshold `w`. Assume `P(E0) > q0` and that
the event of some site of `B ν` above `w` has probability at most `q0 / 2`. Then the events
`E ν ∩ {no site of B ν above w}` are independent over `ν`, each has probability at least
`q0 / 2`, and the probability that all of them fail is at most `exp (-(q0 / 2) N)`. -/
theorem heavy_crossing_trials_indep
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a G0 K w h : ℝ) (hw : 1 ≤ w)
    (I : ℤ) (l m N : ℕ) (hm : 2 * m ≤ l) (c : Fin N → Lattice)
    (hlevel : ∀ ν, (c ν).1 + (c ν).2 = I + (m : ℤ))
    (hround : ∀ ν, |(1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ) -
      (h * w + 30 * ((ν.val + 1 : ℕ) : ℝ) * w)| ≤ 1 / 2)
    (E : Fin N → Set Environment)
    (hE : ∀ ν, E ν = {ω | ∃ (u : Lattice) (d : ℕ × ℕ) (x : Path u d),
      u.1 + u.2 = I + (m : ℤ) ∧ d.1 + d.2 = l - 2 * m ∧
      (∀ k, |(1 - a) * ((x.vertex k).1 : ℝ) - a * ((x.vertex k).2 : ℝ) -
        ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * w) ∧
      G0 * ((l - 2 * m : ℕ) : ℝ) - K * w < pathWeight ω x})
    (E0 : Set Environment)
    (hE0 : E0 = {ω | ∃ (u : Lattice) (d : ℕ × ℕ) (x : Path u d),
      u.1 + u.2 = 0 ∧ d.1 + d.2 = l - 2 * m ∧
      (∀ k, |(1 - a) * ((x.vertex k).1 : ℝ) - a * ((x.vertex k).2 : ℝ)| ≤ 8 * w) ∧
      G0 * ((l - 2 * m : ℕ) : ℝ) - K * w < pathWeight ω x})
    (B : Fin N → Finset Lattice)
    (hB : ∀ ν z, z ∈ B ν ↔ I + (m : ℤ) ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ I + (l : ℤ) - (m : ℤ) ∧
      |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) -
        ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * w)
    (q0 : ℝ) (hq0 : q0 < (environmentLaw μ).real E0)
    (hsmall : ∀ ν, (environmentLaw μ).real {ω : Environment | ¬ ∀ z ∈ B ν, ω z ≤ w} ≤ q0 / 2) :
    iIndepSet (fun ν => E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w}) (environmentLaw μ) ∧
    (∀ ν, q0 / 2 ≤ (environmentLaw μ).real (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w})) ∧
    (environmentLaw μ).real (⋂ ν, (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w})ᶜ) ≤
      Real.exp (-(q0 / 2 * (N : ℝ))) := by
  classical
  obtain ⟨B', hB', -, hdisj', hmeasE, hlocE, hprob, -, -, -⟩ :=
    coarse_crossing_trials μ a G0 K w h hw I l m N hm c hlevel hround E hE E0 hE0
  have hBeq : ∀ ν, B ν = B' ν := fun ν => Finset.ext fun z => (hB ν z).trans (hB' ν z).symm
  have hdisj : Pairwise fun ν ν' => Disjoint (B ν) (B ν') := by
    intro ν ν' hne
    rw [hBeq ν, hBeq ν']
    exact hdisj' hne
  have hloc : ∀ ν (η η' : Environment), (∀ z ∈ B ν, η z = η' z) → (η ∈ E ν ↔ η' ∈ E ν) :=
    fun ν η η' hag => hlocE ν η η' fun z hz => hag z (by rw [hBeq ν]; exact hz)
  have hmeasH : ∀ ν, MeasurableSet {ω : Environment | ∀ z ∈ B ν, ω z ≤ w} :=
    fun ν => measurableSet_no_heavy (B ν) w
  have hA : ∀ ν, MeasurableSet (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w}) :=
    fun ν => (hmeasE ν).inter (hmeasH ν)
  have hlocA : ∀ ν (η η' : Environment), (∀ z ∈ B ν, η z = η' z) →
      (η ∈ E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w} ↔
        η' ∈ E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w}) :=
    fun ν η η' hag => and_congr (hloc ν η η' hag) (no_heavy_local (B ν) w η η' hag)
  have hindA : iIndepSet (fun ν => E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w})
      (environmentLaw μ) :=
    iIndepSet_environment_of_disjoint_supports μ
      (fun ν => E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w}) B hA hlocA hdisj
  have hindC : iIndepSet (fun ν => (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w})ᶜ)
      (environmentLaw μ) :=
    iIndepSet_environment_of_disjoint_supports μ
      (fun ν => (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w})ᶜ) B
      (fun ν => (hA ν).compl) (fun ν η η' hag => not_congr (hlocA ν η η' hag)) hdisj
  have hlow : ∀ ν, q0 / 2 ≤
      (environmentLaw μ).real (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w}) := by
    intro ν
    have hPE : q0 < (environmentLaw μ).real (E ν) := by
      rw [hprob ν]
      exact hq0
    have hsub : E ν ⊆ (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w}) ∪
        {ω : Environment | ¬ ∀ z ∈ B ν, ω z ≤ w} := by
      intro ω hω
      by_cases hs : ∀ z ∈ B ν, ω z ≤ w
      · exact Or.inl ⟨hω, hs⟩
      · exact Or.inr hs
    have hmain : (environmentLaw μ).real (E ν) ≤
        (environmentLaw μ).real (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w}) +
          (environmentLaw μ).real {ω : Environment | ¬ ∀ z ∈ B ν, ω z ≤ w} :=
      (measureReal_mono hsub).trans (measureReal_union_le _ _)
    linarith [hsmall ν]
  have hPone : ∀ ν, (environmentLaw μ).real (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w}) ≤ 1 :=
    fun ν => measureReal_le_one
  have hAll : (environmentLaw μ).real (⋂ ν, (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w})ᶜ) =
      ∏ ν, (1 - (environmentLaw μ).real (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w})) := by
    have hI : (⋂ ν, (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w})ᶜ) =
        ⋂ ν ∈ (Finset.univ : Finset (Fin N)), (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w})ᶜ := by
      simp
    rw [measureReal_def, hI, hindC.meas_biInter Finset.univ, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun ν _ => ?_
    rw [prob_compl_eq_one_sub (hA ν), ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one, measureReal_def]
  have hbound : ∏ ν, (1 - (environmentLaw μ).real (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w})) ≤
      ∏ _ν : Fin N, Real.exp (-(q0 / 2)) := by
    refine Finset.prod_le_prod₀ (fun ν _ => by linarith [hPone ν]) (fun ν _ => ?_)
    linarith [hlow ν, Real.add_one_le_exp (-(q0 / 2))]
  refine ⟨hindA, hlow, ?_⟩
  rw [hAll]
  calc ∏ ν, (1 - (environmentLaw μ).real (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ w}))
      ≤ ∏ _ν : Fin N, Real.exp (-(q0 / 2)) := hbound
    _ = Real.exp (-(q0 / 2 * (N : ℝ))) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
      congr 1
      ring

end LPPDifferentiability

end
