/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.MaximumBoostCount
public import Differentiability.Probability.MaximumModifiedFieldLaw
public import LPP_Foundations.Model.Animals.PathSets
import Mathlib.Tactic.Linarith

/-!
# The boost of a fixed tilt witness

This is one fiber estimate in the proof of Lemma 4.2 of the differentiability
preprint, for one fixed original environment `w`. Raising weights by maximum
resampling never lowers a weight, so a path gains at least `c` times the number
of its fixed good sites whose weight rose by at least `c`. If the witness of the
crossing event gains at least `(K + 16|dr| + 1) s`, the modified environment lies
in the event `calE(s, n)` of strip paths `x_{0:n}` (starting on level `0`) whose
`f_+`-defect is below `-s`. Hence the probability, over the resampling, that the
modified environment misses `calE(s, n)` is at most the binomial lower-tail bound
`4 / lambda`, by Chebyshev's inequality.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace LPPDifferentiability

/-- The weight of a path in the modified environment is at least its original
weight plus `c` times the number of the selected collected sites whose weight
rose by at least `c`. -/
theorem Path.pathWeight_add_mul_boost_count_le {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (R S : Finset Lattice) (hS : S ⊆ p.collectedSites)
    (w w' : Environment) (χ : Lattice → Bool) (c : ℝ) :
    pathWeight w p + c * (∑ v ∈ S, if w v + c ≤
        (if v ∈ R ∧ χ v = true then max (w v) (w' v) else w v) then (1 : ℝ) else 0) ≤
      pathWeight (fun v => if v ∈ R ∧ χ v = true then max (w v) (w' v) else w v) p := by
  have hge : ∀ v, w v ≤ (if v ∈ R ∧ χ v = true then max (w v) (w' v) else w v) :=
    fun v => maximum_modification_ge_original R ((w, w'), χ) v
  have h1 : c * (∑ v ∈ S, if w v + c ≤
        (if v ∈ R ∧ χ v = true then max (w v) (w' v) else w v) then (1 : ℝ) else 0) ≤
      ∑ v ∈ S, ((if v ∈ R ∧ χ v = true then max (w v) (w' v) else w v) - w v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    have hv := hge v
    generalize (if v ∈ R ∧ χ v = true then max (w v) (w' v) else w v) = x at hv ⊢
    split_ifs with h
    · linarith only [h]
    · linarith only [hv]
  have h2 : ∑ v ∈ S, ((if v ∈ R ∧ χ v = true then max (w v) (w' v) else w v) - w v) ≤
      ∑ v ∈ p.collectedSites,
        ((if v ∈ R ∧ χ v = true then max (w v) (w' v) else w v) - w v) :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun v _ _ => sub_nonneg.2 (hge v))
  have h3 : ∑ v ∈ p.collectedSites,
        ((if v ∈ R ∧ χ v = true then max (w v) (w' v) else w v) - w v) =
      ∑ v ∈ p.collectedSites, (if v ∈ R ∧ χ v = true then max (w v) (w' v) else w v) -
        ∑ v ∈ p.collectedSites, w v := by
    rw [Finset.sum_sub_distrib]
  simp only [Path.pathWeight_eq_sum_collectedSites]
  linarith only [h1, h2, h3]

/-- The fiber estimate of the proof of Lemma 4.2 of the differentiability preprint,
for one fixed original environment `w`. If `q` is a path `x_{0:n}` from a start
`u` on level `0` with every vertex in the strip `|r| ≤ 8s` and weight above
`G0 n - K s`, and `S` is a nonempty set of its collected sites in `R` whose
`w`-weights lie in the good set (a cutoff on the distribution function and a
gap between quantiles), and the boost `c lambda / 2` is at least
`(K + 16|dr| + 1) s`, then the resampling fiber probability that the modified
environment is not in `calE(s, n)` is at most `4 / lambda`, where
`lambda = |S| delta alpha / 2`. -/
theorem tilt_fixed_witness_boost_failure_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {δ α c : ℝ}
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hα : α ∈ Ioo (0 : ℝ) 1) (hc : 0 < c)
    (a s G0 dr K : ℝ) (n : ℕ) (R S : Finset Lattice) (w : Environment)
    {u : Lattice} {e : ℕ × ℕ} (q : Path u e) (hu : u.1 + u.2 = 0) (he : e.1 + e.2 = n)
    (hstrip : ∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s)
    (hweight : G0 * (n : ℝ) - K * s < pathWeight w q)
    (hSq : S ⊆ q.collectedSites) (hSR : S ⊆ R) (hS : S.Nonempty)
    (hF : ∀ v ∈ S, μ.real (Iic (w v)) ≤ 1 - α)
    (hgap : ∀ v ∈ S, c ≤
      sInf {r : ℝ | μ.real (Iic (w v)) + α / 2 ≤ μ.real (Iic r)} - w v)
    (hmean : (K + 16 * |dr| + 1) * s ≤ c * ((S.card : ℝ) * δ * α / 2) / 2) :
    ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
      ENNReal.ofReal (1 - δ) • Measure.dirac false +
        ENNReal.ofReal δ • Measure.dirac true))).real
      {r : Environment × (Lattice → Bool) |
        (fun v => if v ∈ R ∧ r.2 v = true then max (w v) (r.1 v) else w v) ∉
          {ω : Environment | ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧
            ∃ q : Path u e,
              (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s) ∧
              G0 * (((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) +
                  ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ)) +
                dr * ((1 - a) * ((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) -
                  a * ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ)) -
                pathWeight ω q < -s}} ≤
      4 / ((S.card : ℝ) * δ * α / 2) := by
  have hcount := maximum_resampling_fiber_count_lower_tail μ hδ hα hc w R S hSR hS hF hgap
  dsimp only at hcount
  obtain ⟨_, htail⟩ := hcount
  have : IsProbabilityMeasure (ENNReal.ofReal (1 - δ) • Measure.dirac false +
      ENNReal.ofReal δ • Measure.dirac true) :=
    maximum_resampling_coin_is_probability ⟨hδ.1.le, hδ.2.le⟩
  refine le_trans (measureReal_mono ?_) htail
  intro r hr
  simp only [Set.mem_ofPred_eq] at hr ⊢
  by_contra hlow0
  have hlow := not_lt.1 hlow0
  apply hr
  refine ⟨u, hu, e, he, q, hstrip, ?_⟩
  have hgain := Path.pathWeight_add_mul_boost_count_le q R S hSq w r.1 r.2 c
  have hcc := mul_le_mul_of_nonneg_left hlow hc.le
  -- The displacement `x_n - x_0` has level `n` and `|r(x_n - x_0)| ≤ 16 s`.
  have hlev : ((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) +
      ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ) = (n : ℝ) := by
    have h := q.level (Fin.last (e.1 + e.2))
    have hZ : (q.vertex (Fin.last (e.1 + e.2)) - u).1 +
        (q.vertex (Fin.last (e.1 + e.2)) - u).2 = (n : ℤ) := by
      simp only [Prod.fst_sub, Prod.snd_sub, Fin.val_last] at h ⊢
      omega
    exact_mod_cast hZ
  have hr : (1 - a) * ((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) -
      a * ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ) =
      ((1 - a) * ((q.vertex (Fin.last (e.1 + e.2))).1 : ℝ) -
        a * ((q.vertex (Fin.last (e.1 + e.2))).2 : ℝ)) -
      ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)) := by
    simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
    ring
  have hend := hstrip (Fin.last (e.1 + e.2))
  have hstart := hstrip 0
  rw [q.start] at hstart
  have hdr : dr * ((1 - a) * ((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) -
      a * ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ)) ≤ 16 * |dr| * s := by
    rw [hr]
    have h1 : dr * (((1 - a) * ((q.vertex (Fin.last (e.1 + e.2))).1 : ℝ) -
          a * ((q.vertex (Fin.last (e.1 + e.2))).2 : ℝ)) -
        ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))) ≤
        |dr| * |((1 - a) * ((q.vertex (Fin.last (e.1 + e.2))).1 : ℝ) -
          a * ((q.vertex (Fin.last (e.1 + e.2))).2 : ℝ)) -
        ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h2 := abs_le.1 hend
    have h2' := abs_le.1 hstart
    have h3 : |((1 - a) * ((q.vertex (Fin.last (e.1 + e.2))).1 : ℝ) -
          a * ((q.vertex (Fin.last (e.1 + e.2))).2 : ℝ)) -
        ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤ 16 * s := by
      rw [abs_le]
      constructor <;> linarith only [h2.1, h2.2, h2'.1, h2'.2]
    have h4 := mul_le_mul_of_nonneg_left h3 (abs_nonneg dr)
    linarith only [h1, h4]
  rw [hlev]
  linarith only [hweight, hgain, hcc, hmean, hdr]

end LPPDifferentiability
end
