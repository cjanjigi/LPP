/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.GridScaleConnection
public import Differentiability.Probability.GridStaircaseBad
public import Differentiability.Probability.GridFineStaircaseFamily
public import Differentiability.Probability.GridCrossingTrials
public import Differentiability.Model.CoarseCrossingBlocks
public import LPP_Foundations.Model.Paths.HorizontalFirst
public import Differentiability.Analysis.GridScaleCounts
public import Differentiability.Analysis.GridFineCount
public import Differentiability.FinalDraft.Grid.Events
import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-! # The good event at one fine scale, one grid interval and one bin

The fine-scale good event is (5.14) to (5.16) of the differentiability preprint, and
its probability bound is (5.27) of that paper.

For a fine scale (`l < 8 c_* j² w`), a grid level `I` and a bin `h`, the bad event is the union,
over a set of at most `(l + 1) w + 1` representative values of `ρ` in the bin, of the event that
the staircase of that `ρ` has weight below `l E - t`. Outside it, for every `ρ` in the bin and
every pair of sites `z₀`, `z₁` on levels `I` and `I + l` with transverse coordinates in
`(ρ - 1, ρ]`, the one-scale connection of `grid_scale_connection` exists with both defects at
most `C₁ j² w + 2 t` and all vertices within `C₁ j² w` of `ρ`. The bad event has probability at
most `9 c_* j² w² exp (-t² / (16 c_* k² s M²))`, by the bad-staircase bound
`measure_staircase_bad_le` ((5.12) of the differentiability preprint).

The file also contains two finiteness helpers, `exists_finset_int_of_bounded` and `abs_bin_le`,
used to turn the grid levels and the bins into finite sets ((5.3) and (5.10) of that paper).
-/

public section

open MeasureTheory

namespace LPPDifferentiability

/-- The literal fine-scale failure event `eq:goodfine` is measurable and satisfies the
fine probability bound of `eq:goodprob`. Its complement supplies the grid paths. -/
theorem fine_grid_failure_bound_and_paths
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {M : ℝ} (hM : 0 < M) (hb : ∀ᵐ x ∂μ, |x| ≤ M)
    (a G0 E dl dr K t cstar s : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (hE : E = ∫ x : ℝ, x ∂μ) (hcstar : cstar = 50 / min a (1 - a)) (hEG : E ≤ G0)
    (hdl : |dl| ≤ K) (hdr : |dr| ≤ K) (ht : 0 < t)
    (k w j l : ℕ) (hk : 1 ≤ k) (hs : 0 < s) (hw : 2 ≤ w) (hj : 1 ≤ j)
    (hl : (l : ℝ) < 8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)))
    (hlen : (j : ℝ) ^ 2 * (w : ℝ) ≤ (k : ℝ) ^ 2 * s) (I h : ℤ) :
    let Bad := fineGridFailure a E t I h l w
    MeasurableSet Bad ∧
      (environmentLaw μ).real Bad ≤
        Real.exp (-t ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * s * M ^ 2)) *
          (9 * cstar * (j : ℝ) ^ 2 * (w : ℝ) ^ 2) ∧
      ∀ ω : Environment, ω ∉ Bad → ∀ ρ : ℝ, (h : ℝ) * (w : ℝ) ≤ ρ → ρ < ((h : ℝ) + 1) * (w : ℝ) →
        ∀ z₀ z₁ : Lattice,
        (z₀.1 + z₀.2 = I ∧ ρ - 1 < (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ∧
          (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ≤ ρ) →
        (z₁.1 + z₁.2 = I + (l : ℤ) ∧ ρ - 1 < (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ∧
          (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ≤ ρ) →
        ∃ (D : ℕ × ℕ) (y : Path z₀ D),
          z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
          G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
              pathWeight ω y ≤
            (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) * ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
          G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
              pathWeight ω y ≤
            (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) * ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
          ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) - ρ| ≤
            (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) * ((j : ℝ) ^ 2 * (w : ℝ)) := by
  classical
  intro Bad
  have hcpos : 0 < cstar := by
    rw [hcstar]
    have : 0 < min a (1 - a) := lt_min ha₀ (by linarith)
    positivity
  have hc1 : 1 ≤ cstar := by
    have hθ : 0 < min a (1 - a) := lt_min ha₀ (by linarith)
    have hθ2 : min a (1 - a) ≤ 1 / 2 := by
      have h1 := min_le_left a (1 - a)
      have h2 := min_le_right a (1 - a)
      linarith
    rw [hcstar, le_div_iff₀ hθ]
    linarith
  obtain ⟨R, hRc, hRb, hRrep⟩ := fine_staircase_representatives a I l w (by omega) h
  -- the vertex formula of the staircase of `ρ`
  let F : ℝ → ℕ → Lattice := fun ρ i =>
    (⌊ρ + a * ((I + (i : ℤ) : ℤ) : ℝ)⌋, (I + (i : ℤ)) - ⌊ρ + a * ((I + (i : ℤ) : ℤ) : ℝ)⌋)
  let B : ℝ → Set Environment := fun ρ =>
    {ω | ∑ i ∈ Finset.range l, ω (F ρ i) < (l : ℝ) * E - t}
  have hBprob : ∀ ρ : ℝ, (environmentLaw μ).real (B ρ) ≤
      Real.exp (-t ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * s * M ^ 2)) := by
    intro ρ
    obtain ⟨i, q, hv, -, -⟩ := exists_level_transverse_staircase a ρ ha₀ ha₁ I l
    have hil : i.val ≤ l := by have := i.isLt; omega
    have hdl' : i.val + (l - i.val) = l := by omega
    have hset : B ρ = {ω : Environment | pathWeight ω q <
        (((i.val, l - i.val) : ℕ × ℕ).1 + ((i.val, l - i.val) : ℕ × ℕ).2 : ℕ) *
          ∫ x : ℝ, x ∂μ - t} := by
      ext ω
      simp only [B, Set.mem_ofPred_eq]
      rw [path_weight_eq_sum_of_vertex_formula ω q (F ρ) (fun k => hv k)]
      simp only [hdl', hE]
    rw [hset]
    refine measure_staircase_bad_le μ k hM ht hcpos hk hs hb q ?_
    simp only [hdl']
    have h1 : (l : ℝ) ≤ 8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)) := hl.le
    have h2 : 8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)) ≤ 8 * cstar * ((k : ℝ) ^ 2 * s) :=
      mul_le_mul_of_nonneg_left hlen (by positivity)
    linarith
  have hBad : Bad = ⋃ ρ ∈ R, B ρ := by
    ext ω
    constructor
    · rintro ⟨ρ, hlo, hhi, hwgt⟩
      obtain ⟨ρ', hρ'R, hfl⟩ := hRrep ρ hlo hhi
      apply Set.mem_biUnion hρ'R
      change (∑ i ∈ Finset.range l, ω (F ρ' i)) < (l : ℝ) * E - t
      have hsum : (∑ i ∈ Finset.range l, ω (F ρ i)) =
          ∑ i ∈ Finset.range l, ω (F ρ' i) :=
        Finset.sum_congr rfl fun i hi => by simp only [F, hfl i (Finset.mem_range.1 hi).le]
      rw [← hsum]
      exact hwgt
    · intro hω
      obtain ⟨ρ, hρR, hωρ⟩ := Set.mem_iUnion₂.mp hω
      exact ⟨ρ, (hRb ρ hρR).1, (hRb ρ hρR).2, hωρ⟩
  rw [hBad]
  refine ⟨Finset.measurableSet_biUnion _ (fun ρ _ => ?_), ?_, ?_⟩
  · exact measurableSet_lt (Finset.measurable_sum _ fun i _ => measurable_pi_apply (F ρ i))
      measurable_const
  · refine (measureReal_biUnion_finset_le R B).trans ?_
    calc ∑ ρ ∈ R, (environmentLaw μ).real (B ρ) ≤
        ∑ _ρ ∈ R, Real.exp (-t ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * s * M ^ 2)) :=
          Finset.sum_le_sum fun ρ _ => hBprob ρ
      _ = (R.card : ℝ) * Real.exp (-t ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * s * M ^ 2)) := by
          simp
      _ ≤ _ := by
          have hfine : (l : ℝ) < 8 * cstar * (j : ℝ) ^ 2 * (w : ℝ) := by linarith
          have h9 := grid_fine_count_le hc1 hj hw hfine
          rw [mul_comm (R.card : ℝ)]
          exact mul_le_mul_of_nonneg_left (hRc.trans h9) (Real.exp_pos _).le
  · intro ω hω ρ hρ₁ hρ₂ z₀ z₁ hz₀ hz₁
    obtain ⟨ρ', hρ'R, hfl⟩ := hRrep ρ hρ₁ hρ₂
    have hωρ' : ¬ ω ∈ B ρ' := fun hmem => hω (Set.mem_biUnion hρ'R hmem)
    obtain ⟨D, q, hD, hv, hW⟩ := (grid_scale_connection a G0 E dl dr K t cstar ω ha₀ ha₁ hcstar
      hEG hdl hdr ht.le w j l _ hw hj rfl I h ρ hρ₁ hρ₂ z₀ z₁ hz₀ hz₁).1 hl
    refine ⟨D, q, hD, ?_⟩
    have e1 := congrArg Prod.fst hD
    have e2 := congrArg Prod.snd hD
    simp only [Prod.fst_add, Prod.snd_add] at e1 e2
    have hz₀l := hz₀.1
    have hz₁l := hz₁.1
    have hDl : D.1 + D.2 = l := by omega
    have hsum : pathWeight ω q = ∑ i ∈ Finset.range l, ω (F ρ' i) := by
      rw [path_weight_eq_sum_of_vertex_formula ω q (F ρ) (fun k => hv k), hDl]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := hfl i (Finset.mem_range.1 hi).le
      simp only [F, this]
    have hge : (l : ℝ) * E - t ≤ pathWeight ω q := by
      rw [hsum]
      by_contra hlt
      exact hωρ' (not_le.1 hlt)
    exact hW hge

/-- The literal coarse-scale failure event of `eq:goodcoarse` is measurable and satisfies
the coarse probability bound of `eq:goodprob`. Either every crossing trial fails or an
attachment staircase is bad. The path construction uses these same fixed centres. -/
theorem coarse_grid_failure_bound_and_paths
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {M : ℝ} (hM : 0 < M) (hb : ∀ᵐ x ∂μ, |x| ≤ M)
    (a G0 E dl dr K t cstar s q0 : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (hE : E = ∫ x : ℝ, x ∂μ) (hcstar : cstar = 50 / min a (1 - a)) (hEG : E ≤ G0)
    (hdl : |dl| ≤ K) (hdr : |dr| ≤ K) (ht : 0 < t)
    (k w j l : ℕ) (hk : 1 ≤ k) (hs : 0 < s) (hw : 2 ≤ w) (hj : 1 ≤ j)
    (hl : 8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)) ≤ (l : ℝ)) (hell : (l : ℝ) ≤ (w : ℝ) ^ 3 / 2)
    (hlen : (j : ℝ) ^ 2 * (w : ℝ) ≤ (k : ℝ) ^ 2 * s)
    (htrial : ∀ n : ℕ, 1 ≤ n → n < l → q0 < (environmentLaw μ).real {ω : Environment |
      ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * (w : ℝ)) ∧
          G0 * (n : ℝ) - K * (w : ℝ) < pathWeight ω q})
    (I h : ℤ) :
    let Bad := coarseGridFailure a G0 E K t I h l ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊ j w
    MeasurableSet Bad ∧
      (environmentLaw μ).real Bad ≤ Real.exp (-(q0 * (j : ℝ) ^ 2)) +
        Real.exp (-t ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * s * M ^ 2)) *
          (60 * (j : ℝ) ^ 2 * (w : ℝ) ^ 2) ∧
      ∀ ω : Environment, ω ∉ Bad → ∀ ρ : ℝ, (h : ℝ) * (w : ℝ) ≤ ρ → ρ < ((h : ℝ) + 1) * (w : ℝ) →
        ∀ z₀ z₁ : Lattice,
        (z₀.1 + z₀.2 = I ∧ ρ - 1 < (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ∧
          (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ≤ ρ) →
        (z₁.1 + z₁.2 = I + (l : ℤ) ∧ ρ - 1 < (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ∧
          (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ≤ ρ) →
        ∃ (D : ℕ × ℕ) (y : Path z₀ D),
          z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
          G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
              pathWeight ω y ≤
            (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) * ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
          G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
              pathWeight ω y ≤
            (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) * ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
          ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) - ρ| ≤
            (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) * ((j : ℝ) ^ 2 * (w : ℝ)) := by
  classical
  intro Bad
  subst hE
  have hθ : 0 < min a (1 - a) := lt_min ha₀ (by linarith)
  have hθ2 : min a (1 - a) ≤ 1 / 2 := by
    have h1 := min_le_left a (1 - a)
    have h2 := min_le_right a (1 - a)
    linarith
  have hcpos : 0 < cstar := by rw [hcstar]; positivity
  have hc100 : 100 ≤ cstar := by
    rw [hcstar, le_div_iff₀ hθ]
    linarith
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast (by omega : 1 ≤ w)
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hP : (1 : ℝ) ≤ (j : ℝ) ^ 2 * (w : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj1) hw1
  have hcP : 100 ≤ cstar * ((j : ℝ) ^ 2 * (w : ℝ)) := by
    have := mul_le_mul hc100 hP (by norm_num) hcpos.le
    linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊ := ⟨_, rfl⟩
  have hmge : cstar * ((j : ℝ) ^ 2 * (w : ℝ)) ≤ (m : ℝ) := by rw [hm]; exact Nat.le_ceil _
  have hmlt : (m : ℝ) < cstar * ((j : ℝ) ^ 2 * (w : ℝ)) + 1 := by
    rw [hm]; exact Nat.ceil_lt_add_one (by positivity)
  have hml : 2 * m < l := by
    have : ((2 * m : ℕ) : ℝ) < l := by push_cast; linarith
    exact_mod_cast this
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  let c : Fin (j ^ 2) → Lattice := fun ν => coarseCrossingCentre a h w I m (ν.val + 1)
  have hlevel (ν : Fin (j ^ 2)) : (c ν).1 + (c ν).2 = I + (m : ℤ) :=
    (coarse_crossing_centre_spec a h w I m (ν.val + 1)).1
  have hround (ν : Fin (j ^ 2)) : |(1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ) -
      ((h : ℝ) * (w : ℝ) + 30 * ((ν.val + 1 : ℕ) : ℝ) * (w : ℝ))| ≤ 1 / 2 :=
    (coarse_crossing_centre_spec a h w I m (ν.val + 1)).2
  let Ev : Fin (j ^ 2) → Set Environment := fun ν => gridCrossingTrial a G0 K w I l m (c ν)
  let E0 : Set Environment := {ω | ∃ (u : Lattice) (d : ℕ × ℕ) (x : Path u d),
    u.1 + u.2 = 0 ∧ d.1 + d.2 = l - 2 * m ∧
    (∀ k, |(1 - a) * ((x.vertex k).1 : ℝ) - a * ((x.vertex k).2 : ℝ)| ≤ 8 * (w : ℝ)) ∧
    G0 * ((l - 2 * m : ℕ) : ℝ) - K * (w : ℝ) < pathWeight ω x}
  obtain ⟨-, -, -, -, hEvmeas, -, -, -, -, hbound⟩ :=
    coarse_crossing_trials μ a G0 K (w : ℝ) (h : ℝ) hw1 I l m (j ^ 2) hml.le c hlevel hround
      Ev (fun ν => rfl) E0 rfl
  have hE0 : q0 < (environmentLaw μ).real E0 := by
    have hset : E0 = {ω : Environment |
        ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = l - 2 * m ∧ ∃ q : Path u e,
          (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * (w : ℝ)) ∧
            G0 * ((l - 2 * m : ℕ) : ℝ) - K * (w : ℝ) < pathWeight ω q} := by
      ext ω
      simp only [E0, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨u, d, x, hu, hd, hv, hw⟩
        exact ⟨u, hu, d, hd, x, hv, hw⟩
      · rintro ⟨u, hu, d, hd, x, hv, hw⟩
        exact ⟨u, d, x, hu, hd, hv, hw⟩
    rw [hset]
    exact htrial (l - 2 * m) (by omega) (by omega)
  obtain ⟨F, hFc, hFm⟩ := coarse_attachment_staircases a I l m j w h c
  let BS : Lattice × (ℕ × ℕ) → Set Environment := fun p =>
    {ω | pathWeight ω (horizontalFirst p.1 p.2) <
      ((p.2.1 + p.2.2 : ℕ) : ℝ) * ∫ x : ℝ, x ∂μ - t}
  have hBS : ∀ p ∈ F, (environmentLaw μ).real (BS p) ≤
      Real.exp (-t ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * s * M ^ 2)) := by
    intro p hp
    have hpm := isCoarseAttachmentStaircase_length ((hFm p).1 hp)
    refine measure_staircase_bad_le μ k hM ht hcpos hk hs hb (horizontalFirst p.1 p.2) ?_
    rw [hpm]
    have h2 : cstar * ((j : ℝ) ^ 2 * (w : ℝ)) ≤ cstar * ((k : ℝ) ^ 2 * s) :=
      mul_le_mul_of_nonneg_left hlen hcpos.le
    linarith
  have hcount : (F.card : ℝ) ≤ 60 * (j : ℝ) ^ 2 * (w : ℝ) ^ 2 := by
    have h3 : F.card ≤ 60 * j ^ 2 * w ^ 2 := hFc.trans (grid_staircase_count_le j hw)
    exact_mod_cast h3
  have hBad : Bad = (⋂ ν, (Ev ν)ᶜ) ∪ ⋃ p ∈ F, BS p := by
    have hstairs : {ω | ∃ p : Lattice × (ℕ × ℕ),
        IsCoarseAttachmentStaircase a I l m j w h c p ∧ ω ∈ BS p} = ⋃ p ∈ F, BS p := by
      ext ω
      constructor
      · rintro ⟨p, hp, hwgt⟩
        exact Set.mem_biUnion ((hFm p).2 hp) hwgt
      · intro hω
        obtain ⟨p, hp, hwgt⟩ := Set.mem_iUnion₂.mp hω
        exact ⟨p, (hFm p).1 hp, hwgt⟩
    change coarseGridFailure a G0 (∫ x : ℝ, x ∂μ) K t I h l
      ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊ j w = _
    rw [← hm]
    exact congrArg ((⋂ ν, (Ev ν)ᶜ) ∪ ·) hstairs
  rw [hBad]
  refine ⟨(MeasurableSet.iInter fun ν => (hEvmeas ν).compl).union
    (Finset.measurableSet_biUnion _ fun p _ => measurableSet_lt
      (measurable_pathWeight (horizontalFirst p.1 p.2)) measurable_const), ?_, ?_⟩
  · refine (measureReal_union_le _ _).trans ?_
    have h1 : (environmentLaw μ).real (⋂ ν, (Ev ν)ᶜ) ≤ Real.exp (-(q0 * (j : ℝ) ^ 2)) := by
      have hc : ((j ^ 2 : ℕ) : ℝ) = (j : ℝ) ^ 2 := by push_cast; ring
      have := hbound q0 hE0
      rw [hc] at this
      exact this
    have h2 : (environmentLaw μ).real (⋃ p ∈ F, BS p) ≤
        Real.exp (-t ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * s * M ^ 2)) *
          (60 * (j : ℝ) ^ 2 * (w : ℝ) ^ 2) := by
      refine (measureReal_biUnion_finset_le F BS).trans ?_
      calc ∑ p ∈ F, (environmentLaw μ).real (BS p) ≤
          ∑ _p ∈ F, Real.exp (-t ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * s * M ^ 2)) :=
            Finset.sum_le_sum fun p hp => hBS p hp
        _ = (F.card : ℝ) * Real.exp (-t ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * s * M ^ 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := by
            rw [mul_comm (F.card : ℝ)]
            exact mul_le_mul_of_nonneg_left hcount (Real.exp_pos _).le
    linarith
  · intro ω hω ρ hρ₁ hρ₂ z₀ z₁ hz₀ hz₁
    have hω1 : ω ∉ ⋂ ν, (Ev ν)ᶜ := fun h' => hω (Or.inl h')
    have hω2 : ∀ p ∈ F, ω ∉ BS p := fun p hp h' => hω (Or.inr (Set.mem_biUnion hp h'))
    obtain ⟨ν, hν⟩ : ∃ ν, ω ∈ Ev ν := by
      by_contra hcon
      simp only [not_exists] at hcon
      exact hω1 (Set.mem_iInter.2 hcon)
    obtain ⟨u, d, x, hu, hd, hx, hW⟩ := hν
    obtain ⟨d₁, d₂, h1, h2, hk'⟩ := (grid_scale_connection a G0 _ dl dr K t cstar ω ha₀ ha₁
      hcstar hEG hdl hdr ht.le w j l m hw hj hm I h ρ hρ₁ hρ₂ z₀ z₁ hz₀ hz₁).2 hl hell c hlevel
      hround ν u d x hu hd hx hW
    have e1 := congrArg Prod.fst h1
    have e2 := congrArg Prod.snd h1
    have f1 := congrArg Prod.fst h2
    have f2 := congrArg Prod.snd h2
    simp only [Prod.fst_add, Prod.snd_add] at e1 e2 f1 f2
    have hz₀l := hz₀.1
    have hz₁l := hz₁.1
    have hd₁s : d₁.1 + d₁.2 = m := by omega
    have hd₂s : d₂.1 + d₂.2 = m := by omega
    have hru : |(1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) -
        ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * (w : ℝ) := by
      have h0 := hx ⟨0, by omega⟩
      rw [show (⟨0, by omega⟩ : Fin (d.1 + d.2 + 1)) = 0 from rfl, x.start] at h0
      exact h0
    have hru' : |(1 - a) * ((u + ((d.1 : ℤ), (d.2 : ℤ))).1 : ℝ) -
        a * ((u + ((d.1 : ℤ), (d.2 : ℤ))).2 : ℝ) -
        ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * (w : ℝ) := by
      have h0 := hx (Fin.last (d.1 + d.2))
      rw [x.finish] at h0
      exact h0
    have hu' : (u + ((d.1 : ℤ), (d.2 : ℤ))).1 + (u + ((d.1 : ℤ), (d.2 : ℤ))).2 =
        I + (l : ℤ) - (m : ℤ) := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    have hmem1 : (z₀, d₁) ∈ F := by
      apply (hFm _).2
      simp only [IsCoarseAttachmentStaircase, h1]
      exact Or.inl ⟨⟨hz₀l, by linarith [hz₀.2.1], by linarith [hz₀.2.2]⟩, ν, hu, hru⟩
    have hmem2 : (u + ((d.1 : ℤ), (d.2 : ℤ)), d₂) ∈ F := by
      apply (hFm _).2
      simp only [IsCoarseAttachmentStaircase, h2]
      exact Or.inr ⟨⟨ν, hu', hru'⟩, hz₁l, by linarith [hz₁.2.1], by linarith [hz₁.2.2]⟩
    have w1 : (m : ℝ) * ∫ x : ℝ, x ∂μ - t ≤ pathWeight ω (horizontalFirst z₀ d₁) := by
      by_contra hlt
      refine hω2 (z₀, d₁) hmem1 ?_
      show pathWeight ω (horizontalFirst z₀ d₁) < ((d₁.1 + d₁.2 : ℕ) : ℝ) * ∫ x : ℝ, x ∂μ - t
      rw [hd₁s]
      exact not_le.1 hlt
    have w2 : (m : ℝ) * ∫ x : ℝ, x ∂μ - t ≤
        pathWeight ω (horizontalFirst (u + ((d.1 : ℤ), (d.2 : ℤ))) d₂) := by
      by_contra hlt
      refine hω2 (u + ((d.1 : ℤ), (d.2 : ℤ)), d₂) hmem2 ?_
      show pathWeight ω (horizontalFirst (u + ((d.1 : ℤ), (d.2 : ℤ))) d₂) <
        ((d₂.1 + d₂.2 : ℕ) : ℝ) * ∫ x : ℝ, x ∂μ - t
      rw [hd₂s]
      exact not_le.1 hlt
    exact hk' w1 w2

/-- A counted bad event and the paths on its complement. -/
theorem grid_good_event_fine
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {M : ℝ} (hM : 0 < M) (hb : ∀ᵐ x ∂μ, |x| ≤ M)
    (a G0 E dl dr K t cstar s : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (hE : E = ∫ x : ℝ, x ∂μ) (hcstar : cstar = 50 / min a (1 - a)) (hEG : E ≤ G0)
    (hdl : |dl| ≤ K) (hdr : |dr| ≤ K) (ht : 0 < t)
    (k w j l : ℕ) (hk : 1 ≤ k) (hs : 0 < s) (hw : 2 ≤ w) (hj : 1 ≤ j)
    (hl : (l : ℝ) < 8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)))
    (hlen : (j : ℝ) ^ 2 * (w : ℝ) ≤ (k : ℝ) ^ 2 * s) (I h : ℤ) :
    ∃ Bad : Set Environment,
      (environmentLaw μ).real Bad ≤
        Real.exp (-t ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * s * M ^ 2)) *
          (9 * cstar * (j : ℝ) ^ 2 * (w : ℝ) ^ 2) ∧
      ∀ ω : Environment, ω ∉ Bad → ∀ ρ : ℝ, (h : ℝ) * (w : ℝ) ≤ ρ → ρ < ((h : ℝ) + 1) * (w : ℝ) →
        ∀ z₀ z₁ : Lattice,
        (z₀.1 + z₀.2 = I ∧ ρ - 1 < (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ∧
          (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ≤ ρ) →
        (z₁.1 + z₁.2 = I + (l : ℤ) ∧ ρ - 1 < (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ∧
          (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ≤ ρ) →
        ∃ (D : ℕ × ℕ) (y : Path z₀ D),
          z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
          G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
              pathWeight ω y ≤
            (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) * ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
          G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
              pathWeight ω y ≤
            (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) * ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
          ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) - ρ| ≤
            (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) * ((j : ℝ) ^ 2 * (w : ℝ)) := by
  exact ⟨fineGridFailure a E t I h l w, (fine_grid_failure_bound_and_paths μ hM hb
    a G0 E dl dr K t cstar s ha₀ ha₁ hE hcstar hEG hdl hdr ht k w j l hk hs hw hj hl hlen I h).2⟩

/-- A counted bad event and the paths on its complement. -/
theorem grid_good_event_coarse
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {M : ℝ} (hM : 0 < M) (hb : ∀ᵐ x ∂μ, |x| ≤ M)
    (a G0 E dl dr K t cstar s q0 : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (hE : E = ∫ x : ℝ, x ∂μ) (hcstar : cstar = 50 / min a (1 - a)) (hEG : E ≤ G0)
    (hdl : |dl| ≤ K) (hdr : |dr| ≤ K) (ht : 0 < t)
    (k w j l : ℕ) (hk : 1 ≤ k) (hs : 0 < s) (hw : 2 ≤ w) (hj : 1 ≤ j)
    (hl : 8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)) ≤ (l : ℝ)) (hell : (l : ℝ) ≤ (w : ℝ) ^ 3 / 2)
    (hlen : (j : ℝ) ^ 2 * (w : ℝ) ≤ (k : ℝ) ^ 2 * s)
    (htrial : ∀ n : ℕ, 1 ≤ n → n < l → q0 < (environmentLaw μ).real {ω : Environment |
      ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * (w : ℝ)) ∧
          G0 * (n : ℝ) - K * (w : ℝ) < pathWeight ω q})
    (I h : ℤ) :
    ∃ Bad : Set Environment,
      (environmentLaw μ).real Bad ≤ Real.exp (-(q0 * (j : ℝ) ^ 2)) +
        Real.exp (-t ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * s * M ^ 2)) *
          (60 * (j : ℝ) ^ 2 * (w : ℝ) ^ 2) ∧
      ∀ ω : Environment, ω ∉ Bad → ∀ ρ : ℝ, (h : ℝ) * (w : ℝ) ≤ ρ → ρ < ((h : ℝ) + 1) * (w : ℝ) →
        ∀ z₀ z₁ : Lattice,
        (z₀.1 + z₀.2 = I ∧ ρ - 1 < (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ∧
          (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ≤ ρ) →
        (z₁.1 + z₁.2 = I + (l : ℤ) ∧ ρ - 1 < (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ∧
          (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ≤ ρ) →
        ∃ (D : ℕ × ℕ) (y : Path z₀ D),
          z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
          G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
              pathWeight ω y ≤
            (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) * ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
          G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
              pathWeight ω y ≤
            (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) * ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
          ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) - ρ| ≤
            (8 * cstar * (G0 - E) + 2 * K + 3 * cstar) * ((j : ℝ) ^ 2 * (w : ℝ)) := by
  exact ⟨coarseGridFailure a G0 E K t I h l ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊ j w, (coarse_grid_failure_bound_and_paths μ hM hb
    a G0 E dl dr K t cstar s q0 ha₀ ha₁ hE hcstar hEG hdl hdr ht k w j l hk hs hw hj hl hell hlen htrial I h).2⟩

/-- A set of integers all of whose members are bounded in absolute value is a `Finset`. -/
theorem exists_finset_int_of_bounded (Q : ℤ → Prop) (B : ℝ)
    (hQ : ∀ h, Q h → |(h : ℝ)| ≤ B) : ∃ S : Finset ℤ, ∀ h, h ∈ S ↔ Q h := by
  classical
  refine ⟨(Finset.Icc (-⌈B⌉) ⌈B⌉).filter Q, fun h => ?_⟩
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨fun hh => hh.2, fun hh => ⟨?_, hh⟩⟩
  have h1 := abs_le.1 (hQ h hh)
  have h2 : (h : ℝ) ≤ ⌈B⌉ := h1.2.trans (Int.le_ceil B)
  have h3 : -(⌈B⌉ : ℝ) ≤ h := by linarith [Int.le_ceil B]
  exact ⟨by exact_mod_cast h3, by exact_mod_cast h2⟩

/-- A bin index with a point `x` of `[-X, X]` in its bin has `|h| ≤ X + 1`. -/
theorem abs_bin_le {X W x : ℝ} (hX : 0 ≤ X) (hW : 1 ≤ W) {h : ℤ}
    (h1 : (h : ℝ) * W ≤ x) (h2 : x < ((h : ℝ) + 1) * W) (h3 : |x| ≤ X) : |(h : ℝ)| ≤ X + 1 := by
  obtain ⟨h3a, h3b⟩ := abs_le.1 h3
  rw [abs_le]
  constructor
  · by_contra hcon
    have hneg : (h : ℝ) + 1 ≤ 0 := by linarith
    have := mul_le_mul_of_nonpos_left hW hneg
    linarith
  · by_contra hcon
    have hpos : (0 : ℝ) ≤ h := by linarith
    have := mul_le_mul_of_nonneg_left hW hpos
    linarith

end LPPDifferentiability
