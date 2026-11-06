/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.PathWeight
public import LPP_Foundations.Probability.DisjointSupportEvents
import Differentiability.Probability.FinitePathMeasurableSelection
import Differentiability.Model.CoarseCrossingBlocks
import Differentiability.Model.FiniteLevelStripCardinality
import LPP_Foundations.Model.Paths.Level
import LPP_Foundations.Model.Paths.Translate
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# The coarse crossing trials of one grid interval

At a coarse scale the grid lemma places `N` crossing trials in blocks around
centres `c ν` on level `I + m`. The trial `E ν` is the event that some path
from level `I + m` of length `l - 2 m` stays within transverse distance `8 w`
of the centre `c ν` and has weight above `G0 (l - 2 m) - K w`. This is the
crossing hypothesis of `coarse_scale_connection`.

`coarse_crossing_trials` shows that each trial is measurable and determined by
the weights on a finite block `B ν`, that the blocks are pairwise disjoint, that
each trial has the probability of one untranslated crossing event, that the
trials are independent, and that all trials fail with probability
`(1 - P E0) ^ N`, which is at most `exp (-q0 N)` whenever `q0 < P E0`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- The transverse coordinate is additive. -/
private theorem transverse_add (a : ℝ) (v z : Lattice) :
    (1 - a) * ((v + z).1 : ℝ) - a * ((v + z).2 : ℝ) =
      ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ)) + ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)) := by
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

/-- Subtracting a centre subtracts its transverse coordinate. -/
private theorem transverse_neg_add (a : ℝ) (v z : Lattice) :
    (1 - a) * ((-v + z).1 : ℝ) - a * ((-v + z).2 : ℝ) =
      ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)) - ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ)) := by
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Int.cast_add, Int.cast_neg]
  ring

/-- Two centres with different indices are more than `16 w` apart. -/
private theorem centre_gap (w h rν rμ : ℝ) (i j : ℕ) (hw : 1 ≤ w) (hij : i ≠ j)
    (hi : |rν - (h * w + 30 * ((i + 1 : ℕ) : ℝ) * w)| ≤ 1 / 2)
    (hj : |rμ - (h * w + 30 * ((j + 1 : ℕ) : ℝ) * w)| ≤ 1 / 2) :
    16 * w < |rν - rμ| := by
  obtain ⟨hi1, hi2⟩ := abs_le.mp hi
  obtain ⟨hj1, hj2⟩ := abs_le.mp hj
  push_cast at hi1 hi2 hj1 hj2
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · have h1 : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
    have h3 : w * ((i : ℝ) + 1) ≤ w * j := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h4 : rμ - rν ≤ |rν - rμ| := by rw [abs_sub_comm]; exact le_abs_self _
    nlinarith
  · have h1 : (j : ℝ) + 1 ≤ i := by exact_mod_cast hgt
    have h3 : w * ((j : ℝ) + 1) ≤ w * i := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h4 : rν - rμ ≤ |rν - rμ| := le_abs_self _
    nlinarith

/-- The untranslated trial event is measurable and determined by the weights on the
block `K0`, which contains every vertex of every path. -/
private theorem untranslated_trial_measurable_local
    (a G0 K w : ℝ) (n : ℕ) (K0 : Finset Lattice)
    (hK0 : ∀ z, z ∈ K0 ↔ 0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 0 + (n : ℤ) ∧
      |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - 0| ≤ 8 * w)
    (E0 : Set Environment)
    (hE0 : E0 = {ω | ∃ (u : Lattice) (d : ℕ × ℕ) (x : Path u d),
      u.1 + u.2 = 0 ∧ d.1 + d.2 = n ∧
      (∀ k, |(1 - a) * ((x.vertex k).1 : ℝ) - a * ((x.vertex k).2 : ℝ)| ≤ 8 * w) ∧
      G0 * (n : ℝ) - K * w < pathWeight ω x}) :
    MeasurableSet E0 ∧
      ∀ ω ω' : Environment, (∀ z ∈ K0, ω z = ω' z) → (ω ∈ E0 ↔ ω' ∈ E0) := by
  have hmem : ∀ (u : Lattice) (d : ℕ × ℕ) (x : Path u d), u.1 + u.2 = 0 → d.1 + d.2 = n →
      (∀ k, |(1 - a) * ((x.vertex k).1 : ℝ) - a * ((x.vertex k).2 : ℝ)| ≤ 8 * w) →
      ∀ k, x.vertex k ∈ K0 := by
    intro u d x hu hd hv k
    have hl := x.level k
    have hk := k.isLt
    exact (hK0 _).mpr ⟨by omega, by omega, by rw [sub_zero]; exact hv k⟩
  have hloc : ∀ ω ω' : Environment, (∀ z ∈ K0, ω z = ω' z) → ω ∈ E0 → ω' ∈ E0 := by
    intro ω ω' h hω
    rw [hE0] at hω ⊢
    obtain ⟨u, d, x, hu, hd, hv, hw⟩ := hω
    refine ⟨u, d, x, hu, hd, hv, ?_⟩
    have hsame : pathWeight ω x = pathWeight ω' x := by
      unfold pathWeight
      exact Finset.sum_congr rfl fun i _ => h _ (hmem u d x hu hd hv _)
    rw [← hsame]
    exact hw
  refine ⟨?_, fun ω ω' h => ⟨hloc ω ω' h, hloc ω' ω fun z hz => (h z hz).symm⟩⟩
  have hEq : E0 = ⋃ u : {u : Lattice // u ∈ K0 ∧ u.1 + u.2 = 0},
      {ω : Environment | ∃ q : Σ i : Fin (n + 1), Path u.1 (i.val, n - i.val),
        (∀ j : Fin (q.1.val + (n - q.1.val) + 1), q.2.vertex j ∈ K0) ∧
          pathWeight ω q.2 > G0 * (n : ℝ) - K * w} := by
    ext ω
    rw [hE0]
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨u, d, x, hu, hd, hv, hw⟩
      obtain ⟨d1, d2⟩ := d
      have hd2 : d2 = n - d1 := by
        have : d1 + d2 = n := hd
        omega
      subst hd2
      have hd1 : d1 < n + 1 := by
        have : d1 + (n - d1) = n := hd
        omega
      have hu0 : u ∈ K0 := by
        have := hmem u _ x hu hd hv 0
        rwa [x.start] at this
      exact ⟨⟨u, hu0, hu⟩, ⟨⟨d1, hd1⟩, x⟩, hmem u _ x hu hd hv, hw⟩
    · rintro ⟨⟨u, hu0, hu⟩, ⟨i, x⟩, hq, hw⟩
      have hi := i.isLt
      refine ⟨u, (i.val, n - i.val), x, hu, by simp only; omega, fun k => ?_, hw⟩
      rw [← sub_zero ((1 - a) * (((x.vertex k).1 : ℤ) : ℝ) - a * (((x.vertex k).2 : ℤ) : ℝ))]
      exact ((hK0 _).mp (hq k)).2.2
  rw [hEq]
  exact MeasurableSet.iUnion fun u =>
    measurableSet_exists_path_in_region_weight_gt u.1 n K0 _

/-- Each trial is the preimage of the untranslated event under translation by its centre. -/
private theorem trial_eq_translate_preimage
    (a G0 K w : ℝ) (I : ℤ) (l m : ℕ) (c : Lattice)
    (hlevel : c.1 + c.2 = I + (m : ℤ))
    (E E0 : Set Environment)
    (hE : E = {ω | ∃ (u : Lattice) (d : ℕ × ℕ) (x : Path u d),
      u.1 + u.2 = I + (m : ℤ) ∧ d.1 + d.2 = l - 2 * m ∧
      (∀ k, |(1 - a) * ((x.vertex k).1 : ℝ) - a * ((x.vertex k).2 : ℝ) -
        ((1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ))| ≤ 8 * w) ∧
      G0 * ((l - 2 * m : ℕ) : ℝ) - K * w < pathWeight ω x})
    (hE0 : E0 = {ω | ∃ (u : Lattice) (d : ℕ × ℕ) (x : Path u d),
      u.1 + u.2 = 0 ∧ d.1 + d.2 = l - 2 * m ∧
      (∀ k, |(1 - a) * ((x.vertex k).1 : ℝ) - a * ((x.vertex k).2 : ℝ)| ≤ 8 * w) ∧
      G0 * ((l - 2 * m : ℕ) : ℝ) - K * w < pathWeight ω x}) :
    E = environmentTranslationEquiv c ⁻¹' E0 := by
  ext ω
  rw [hE, hE0]
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨u, d, x, hu, hd, hv, hw⟩
    obtain ⟨u0, rfl⟩ : ∃ u0, u = c + u0 := ⟨-c + u, by simp⟩
    refine ⟨u0, d, Path.untranslate c x, ?_, hd, fun k => ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.snd_add] at hu
      omega
    · rw [Path.untranslate_vertex, transverse_neg_add]
      exact hv k
    · have h := pathWeight_translate ω (Path.untranslate c x) c
      rw [Path.translate_untranslate] at h
      rw [h] at hw
      exact hw
  · rintro ⟨u0, d, x, hu, hd, hv, hw⟩
    refine ⟨c + u0, d, x.translate c, ?_, hd, fun k => ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.snd_add]
      omega
    · rw [Path.translate_vertex, transverse_add, add_sub_cancel_left]
      exact hv k
    · rw [pathWeight_translate]
      exact hw

/-- **Crossing trials of one coarse grid interval.** Let `c ν`, `ν < N`, be sites on level
`I + m` whose transverse coordinates are within `1/2` of `h w + 30 (ν + 1) w`, as in
`coarse_scale_connection`, and let `E ν` be the event that some path from level `I + m` of
length `l - 2 m` stays within transverse distance `8 w` of `c ν` and has weight above
`G0 (l - 2 m) - K w`. Let `E0` be the same event started on level `0` around the origin.
Then there are finite blocks `B ν` with: the block is the set of sites between levels
`I + m` and `I + l - m` within `8 w` of `c ν`; all vertices of every path lie in
`B ν`; the blocks are pairwise disjoint; each `E ν` is measurable and determined by the
weights on `B ν`; each `E ν` has the probability of `E0`; the `E ν` are independent; all
trials fail with probability `(1 - P E0) ^ N`; and this is at most `exp (-q0 N)` for every
`q0 < P E0`. -/
theorem coarse_crossing_trials
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
      G0 * ((l - 2 * m : ℕ) : ℝ) - K * w < pathWeight ω x}) :
    ∃ B : Fin N → Finset Lattice,
      (∀ ν z, z ∈ B ν ↔ I + (m : ℤ) ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ I + (l : ℤ) - (m : ℤ) ∧
        |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) -
          ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * w) ∧
      (∀ ν (u : Lattice) (d : ℕ × ℕ) (x : Path u d),
        u.1 + u.2 = I + (m : ℤ) → d.1 + d.2 = l - 2 * m →
        (∀ k, |(1 - a) * ((x.vertex k).1 : ℝ) - a * ((x.vertex k).2 : ℝ) -
          ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * w) →
        ∀ k, x.vertex k ∈ B ν) ∧
      (Pairwise fun ν ν' => Disjoint (B ν) (B ν')) ∧
      (∀ ν, MeasurableSet (E ν)) ∧
      (∀ ν (ω ω' : Environment), (∀ z ∈ B ν, ω z = ω' z) → (ω ∈ E ν ↔ ω' ∈ E ν)) ∧
      (∀ ν, (environmentLaw μ).real (E ν) = (environmentLaw μ).real E0) ∧
      iIndepSet E (environmentLaw μ) ∧
      (environmentLaw μ).real (⋂ ν, (E ν)ᶜ) = (1 - (environmentLaw μ).real E0) ^ N ∧
      (∀ q0 : ℝ, q0 < (environmentLaw μ).real E0 →
        (environmentLaw μ).real (⋂ ν, (E ν)ᶜ) ≤ Real.exp (-(q0 * (N : ℝ)))) := by
  classical
  obtain ⟨K0, hK0r, -⟩ := exists_finset_signed_level_tube a (8 * w) (fun _ => (0 : ℝ)) 0
    (l - 2 * m) (by linarith)
  have hK0 : ∀ z, z ∈ K0 ↔ 0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 0 + ((l - 2 * m : ℕ) : ℤ) ∧
      |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - 0| ≤ 8 * w := fun z => hK0r z
  obtain ⟨hmeas0, hloc0⟩ :=
    untranslated_trial_measurable_local a G0 K w (l - 2 * m) K0 hK0 E0 hE0
  have hEeq : ∀ ν, E ν = environmentTranslationEquiv (c ν) ⁻¹' E0 := fun ν =>
    trial_eq_translate_preimage a G0 K w I l m (c ν) (hlevel ν) (E ν) E0 (hE ν) hE0
  obtain ⟨B, hBdef⟩ : ∃ B : Fin N → Finset Lattice,
      ∀ ν, B ν = K0.map (addLeftEmbedding (c ν)) := ⟨_, fun _ => rfl⟩
  have hB : ∀ ν z, z ∈ B ν ↔ I + (m : ℤ) ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ I + (l : ℤ) - (m : ℤ) ∧
      |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) -
        ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * w := by
    intro ν z
    rw [hBdef ν, Finset.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨h1, h2, h3⟩ := (hK0 y).mp hy
      have hc := hlevel ν
      have hr := transverse_add a (c ν) y
      have hz : (addLeftEmbedding (c ν)) y = c ν + y := rfl
      rw [hz]
      refine ⟨?_, ?_, ?_⟩
      · simp only [Prod.fst_add, Prod.snd_add]
        omega
      · simp only [Prod.fst_add, Prod.snd_add]
        omega
      · rw [hr, add_sub_cancel_left]
        simpa only [sub_zero] using h3
    · rintro ⟨h1, h2, h3⟩
      refine ⟨-c ν + z, (hK0 _).mpr ⟨?_, ?_, ?_⟩, add_neg_cancel_left (c ν) z⟩
      · have hc := hlevel ν
        simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
        omega
      · have hc := hlevel ν
        simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
        omega
      · rw [transverse_neg_add, sub_zero]
        exact h3
  have hdisj : Pairwise fun ν ν' => Disjoint (B ν) (B ν') := by
    intro ν ν' hne
    rw [Finset.disjoint_left]
    intro z hzν hzμ
    have h1 := ((hB ν z).mp hzν).2.2
    have h2 := ((hB ν' z).mp hzμ).2.2
    have hgap := centre_gap w h _ _ ν.val ν'.val hw (fun e => hne (Fin.ext e))
      (hround ν) (hround ν')
    have h3 := abs_sub_le ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))
      ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ))
      ((1 - a) * ((c ν').1 : ℝ) - a * ((c ν').2 : ℝ))
    rw [abs_sub_comm _ ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ))] at h3
    linarith
  have hmeasE : ∀ ν, MeasurableSet (E ν) := fun ν => by
    rw [hEeq ν]
    exact (environmentTranslationEquiv (c ν)).measurable hmeas0
  have hlocE : ∀ ν (ω ω' : Environment), (∀ z ∈ B ν, ω z = ω' z) → (ω ∈ E ν ↔ ω' ∈ E ν) := by
    intro ν ω ω' hag
    rw [hEeq ν]
    refine hloc0 _ _ fun z hz => hag (c ν + z) ?_
    rw [hBdef ν]
    exact Finset.mem_map.mpr ⟨z, hz, rfl⟩
  have hdisjK : Pairwise fun ν ν' => Disjoint (K0.map (addLeftEmbedding (c ν)))
      (K0.map (addLeftEmbedding (c ν'))) := fun ν ν' hne => by
    have hd : Disjoint (B ν) (B ν') := hdisj hne
    rw [hBdef ν, hBdef ν'] at hd
    exact hd
  have hall : (environmentLaw μ).real (⋂ ν, (E ν)ᶜ) =
      (1 - (environmentLaw μ).real E0) ^ N := by
    have key := environmentLaw_iInter_translate_compl μ E0 K0 hmeas0 hloc0 N c hdisjK
    simpa only [hEeq] using key
  refine ⟨B, hB, ?_, hdisj, hmeasE, hlocE, ?_,
    iIndepSet_environment_of_disjoint_supports μ E B hmeasE hlocE hdisj, hall, ?_⟩
  · intro ν u d x hu hd hv k
    rw [hB]
    have hl := x.level k
    have hk := k.isLt
    exact ⟨by omega, by omega, hv k⟩
  · intro ν
    rw [hEeq ν, measureReal_def, measureReal_def,
      (measurePreserving_environmentTranslationEquiv μ (c ν)).measure_preimage_equiv]
  · intro q0 hq0
    rw [hall]
    have hP1 : (environmentLaw μ).real E0 ≤ 1 := measureReal_le_one
    have hP0 : 0 ≤ (environmentLaw μ).real E0 := measureReal_nonneg
    have h1 : 1 - (environmentLaw μ).real E0 ≤ Real.exp (-q0) := by
      have := Real.add_one_le_exp (-q0)
      linarith
    calc (1 - (environmentLaw μ).real E0) ^ N ≤ Real.exp (-q0) ^ N :=
          pow_le_pow_left₀ (by linarith) h1 N
      _ = Real.exp (-(q0 * (N : ℝ))) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring

/-- **Crossing trials in the coarse setting of `coarse_scale_connection`.** Under its hypotheses
(`c_* = 50 / min a (1 - a)`, `m = ⌈c_* j² w⌉`, `8 c_* j² w ≤ l ≤ w³ / 2`) there are centres
`c ν`, `ν < j²`, with the level and rounding properties of `coarse_scale_connection`
and `exists_coarse_crossing_blocks`. For these centres the `j²` trials `E ν` are independent,
each has the probability of the untranslated event `E0`, and all fail with probability
`(1 - P E0) ^ j²`, which is at most `exp (-q0 j²)` for every `q0 < P E0`. -/
theorem coarse_crossing_trials_of_coarse_scale
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a G0 K cstar : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (hcstar : cstar = 50 / min a (1 - a)) (w j l m : ℕ) (hw : 2 ≤ w) (hj : 1 ≤ j)
    (hm : m = ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊)
    (hl : 8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)) ≤ (l : ℝ))
    (hell : (l : ℝ) ≤ (w : ℝ) ^ 3 / 2) (I h : ℤ) :
    ∃ c : Fin (j ^ 2) → Lattice,
      (∀ ν, (c ν).1 + (c ν).2 = I + (m : ℤ)) ∧
      (∀ ν, |(1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ) -
        ((h : ℝ) * (w : ℝ) + 30 * ((ν.val + 1 : ℕ) : ℝ) * (w : ℝ))| ≤ 1 / 2) ∧
      ∀ (E : Fin (j ^ 2) → Set Environment)
        (_ : ∀ ν, E ν = {ω | ∃ (u : Lattice) (d : ℕ × ℕ) (x : Path u d),
          u.1 + u.2 = I + (m : ℤ) ∧ d.1 + d.2 = l - 2 * m ∧
          (∀ k, |(1 - a) * ((x.vertex k).1 : ℝ) - a * ((x.vertex k).2 : ℝ) -
            ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * (w : ℝ)) ∧
          G0 * ((l - 2 * m : ℕ) : ℝ) - K * (w : ℝ) < pathWeight ω x})
        (E0 : Set Environment)
        (_ : E0 = {ω | ∃ (u : Lattice) (d : ℕ × ℕ) (x : Path u d),
          u.1 + u.2 = 0 ∧ d.1 + d.2 = l - 2 * m ∧
          (∀ k, |(1 - a) * ((x.vertex k).1 : ℝ) - a * ((x.vertex k).2 : ℝ)| ≤ 8 * (w : ℝ)) ∧
          G0 * ((l - 2 * m : ℕ) : ℝ) - K * (w : ℝ) < pathWeight ω x}),
        iIndepSet E (environmentLaw μ) ∧
        (∀ ν, (environmentLaw μ).real (E ν) = (environmentLaw μ).real E0) ∧
        (environmentLaw μ).real (⋂ ν, (E ν)ᶜ) =
          (1 - (environmentLaw μ).real E0) ^ (j ^ 2) ∧
        (∀ q0 : ℝ, q0 < (environmentLaw μ).real E0 →
          (environmentLaw μ).real (⋂ ν, (E ν)ᶜ) ≤ Real.exp (-(q0 * ((j ^ 2 : ℕ) : ℝ)))) := by
  have hθ : 0 < min a (1 - a) := lt_min ha₀ (by linarith)
  have hθ2 : min a (1 - a) ≤ 1 / 2 := by
    have h1 := min_le_left a (1 - a)
    have h2 := min_le_right a (1 - a)
    linarith
  have hc100 : 100 ≤ cstar := by
    rw [hcstar, le_div_iff₀ hθ]
    linarith
  have hw1 : (1 : ℝ) ≤ w := by
    have : (2 : ℝ) ≤ w := by exact_mod_cast hw
    linarith
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hP : (1 : ℝ) ≤ (j : ℝ) ^ 2 * (w : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj1) hw1
  have hX : 100 ≤ cstar * ((j : ℝ) ^ 2 * (w : ℝ)) := by nlinarith
  have hmlt : (m : ℝ) < cstar * ((j : ℝ) ^ 2 * (w : ℝ)) + 1 := by
    rw [hm]
    exact Nat.ceil_lt_add_one (by linarith)
  have hml : 2 * m < l := by
    have : ((2 * m : ℕ) : ℝ) < l := by
      push_cast
      linarith
    exact_mod_cast this
  obtain ⟨c, B, hlevel, hround, -, -, -, -, -⟩ :=
    exists_coarse_crossing_blocks a (h : ℝ) (w : ℝ) I l m (j ^ 2) hw1 hml hell
  refine ⟨c, hlevel, hround, fun E hE E0 hE0 => ?_⟩
  obtain ⟨-, -, -, -, -, -, hprob, hind, hall, hbound⟩ :=
    coarse_crossing_trials μ a G0 K (w : ℝ) (h : ℝ) hw1 I l m (j ^ 2) hml.le c hlevel hround
      E hE E0 hE0
  exact ⟨hind, hprob, hall, hbound⟩

end LPPDifferentiability
