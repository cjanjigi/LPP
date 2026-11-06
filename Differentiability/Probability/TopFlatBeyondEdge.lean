/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.StartSetDeviation
public import Differentiability.Probability.HalfLineEdge
public import Differentiability.Probability.FlatShapeAdapters
public import Differentiability.Probability.TopIndicatorShape
public import LPP_Foundations.Probability.EnvironmentMap
public import LPP_Foundations.Shape.Uniqueness
public import Differentiability.Model.OrientedPercolationLaws
public import LPP_Foundations.Frozen.Analysis.ToQuadrant
import Mathlib.Tactic

/-!
# The top-field shape equals one at or beyond the edge speed

Let `β` be the infimum over `n` of `E a_{n+1} / (n+1)`, where `a_n` is the half-line edge
of the open top sites. This module proves that the shape function `gtop` of the 0/1 top
field takes the value `1` at some direction `(x, 1 - x)` with `x ≥ β`.

The argument has four steps.
1. The edge `a_N` is at most `N`, and its mean is at least `β N`. Markov's inequality on
   `N - a_N` gives an event of probability bounded below, independent of `N`, on which
   `a_N ≥ (β - η) N`.
2. The start-set deviation bound, applied to the top field, makes the deviation
   variable small with high probability. So some environment has both properties and a
   nonempty reached set.
3. In that environment the site with the largest first coordinate is reached from a
   half-line start `(-k, k)` with `k ≤ C N` by an open path. That path collects `N` top
   weights, so the deviation bound forces `gtop` to be close to `1` at the direction
   `(i/N, 1 - i/N)` with `i/N ≥ β - η`.
4. Compactness and continuity of `gtop` give a direction with value exactly `1`. The upper
   bound `gtop ≤ 1` comes from the shape adapters.

The edge-speed result that the paper cites from the published literature is taken
as given here, not proved.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- If the reached set at level `N` is nonempty, the largest first coordinate is attained
at a site reached from a half-line start `(-k, k)` by an open path with `i` right steps,
where `a_N + k = i ≤ N`. -/
private theorem exists_edge_witness (ω : Environment) (N : ℕ)
    (hne : (openReachSet (topSites ω) antidiagHalfLine N).Nonempty) :
    ∃ k i : ℕ, i ≤ N ∧ halfLineEdge ω N + (k : ℤ) = i ∧
      OpenReach (topSites ω) (-(k : ℤ), (k : ℤ))
        ((-(k : ℤ), (k : ℤ)) + ((i : ℤ), ((N - i : ℕ) : ℤ))) := by
  have hb : BddAbove (Prod.fst '' openReachSet (topSites ω) antidiagHalfLine N) :=
    ⟨0 + N, by
      rintro _ ⟨v, hv, rfl⟩
      exact bddAbove_fst_openReachSet (topSites ω) antidiagHalfLine N 0
        (fun u hu => (show u.1 + u.2 = 0 ∧ u.1 ≤ 0 from hu).2) v hv⟩
  obtain ⟨v, hv, hvv⟩ := maxFirst_mem _ hne hb
  obtain ⟨u, hu, ⟨d, hd, p, hp⟩, hlev⟩ := hv
  have hu' : u.1 + u.2 = 0 ∧ u.1 ≤ 0 := hu
  have h1 := congrArg Prod.fst hd
  have h2 := congrArg Prod.snd hd
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  have hdN : d.1 + d.2 = N := by omega
  have hH : halfLineEdge ω N = v.1 := hvv.symm
  have hueq : u = (-(((-u.1).toNat : ℕ) : ℤ), (((-u.1).toNat : ℕ) : ℤ)) :=
    Prod.ext (by show u.1 = -(((-u.1).toNat : ℕ) : ℤ); omega)
      (by show u.2 = (((-u.1).toNat : ℕ) : ℤ); omega)
  have hN2 : N - d.1 = d.2 := by omega
  refine ⟨(-u.1).toNat, d.1, by omega, by omega, ?_⟩
  rw [hN2, ← hueq, hd]
  exact ⟨d, hd, p, hp⟩

/-- In an environment with a reached start close to the edge, the deviation bound `D`
forces `g` to be large at a direction `(i, N - i)` with `a_N ≤ i ≤ N`. -/
private theorem exists_direction_of_edge (g : Quadrant → ℝ) (ω : Environment) (N C : ℕ)
    (hne : (openReachSet (topSites ω) antidiagHalfLine N).Nonempty)
    (hk : (N : ℤ) - halfLineEdge ω N ≤ (C : ℤ) * N) (D : ℝ)
    (hD : ∀ (k : Fin (C * N + 1)) (i : Fin (N + 1)),
      lastPassage (topField ω) (-(k : ℤ), (k : ℤ)) ((i : ℕ), N - i) -
        topField ω (-(k : ℤ), (k : ℤ)) +
        topField ω ((-(k : ℤ), (k : ℤ)) + (((i : ℕ) : ℤ), ((N - i : ℕ) : ℤ))) -
        g (((i : ℕ) : ℝ≥0), ((N - i : ℕ) : ℝ≥0)) ≤ D) :
    ∃ i : ℕ, i ≤ N ∧ (halfLineEdge ω N : ℝ) ≤ i ∧
      (N : ℝ) - D ≤ g ((i : ℝ≥0), ((N - i : ℕ) : ℝ≥0)) := by
  obtain ⟨k, i, hiN, hki, hreach⟩ := exists_edge_witness ω N hne
  have hkC : k ≤ C * N := by
    have h : (k : ℤ) ≤ (C : ℤ) * (N : ℤ) := by omega
    exact_mod_cast h
  have hp := (openReach_iff_topField_passage ω (-(k : ℤ), (k : ℤ)) (i, N - i)).1 hreach
  have hD' := hD ⟨k, Nat.lt_succ_of_le hkC⟩ ⟨i, Nat.lt_succ_of_le hiN⟩
  have hcast : ((i + (N - i) : ℕ) : ℝ) = N := by
    rw [Nat.add_sub_cancel' hiN]
  dsimp only at hp hD'
  refine ⟨i, hiN, ?_, ?_⟩
  · have h : halfLineEdge ω N ≤ (i : ℤ) := by omega
    exact_mod_cast h
  · linarith

/-- The top field has a deviation variable `D` with the properties of the start-set
deviation bound: nonnegative, above every listed deviation, integrable, and of mean
`o(N)`. -/
private theorem exists_top_deviation (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (gtop : Quadrant → ℝ) (htcont : Continuous gtop)
    (hthom : ∀ (c : ℝ≥0) (x : Quadrant), gtop (c * x.1, c * x.2) = (c : ℝ) * gtop x)
    (htconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * gtop x + (t : ℝ) * gtop y ≤ gtop (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (htshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage (topField ω) 0 d - gtop ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (C : ℕ) :
    ∃ D : ℕ → Environment → ℝ, (∀ N ω, 0 ≤ D N ω) ∧
      (∀ (N : ℕ) (ω : Environment) (k : Fin (C * N + 1)) (i : Fin (N + 1)),
        lastPassage (topField ω) (-(k : ℤ), (k : ℤ)) ((i : ℕ), N - i) -
          topField ω (-(k : ℤ), (k : ℤ)) +
          topField ω ((-(k : ℤ), (k : ℤ)) + (((i : ℕ) : ℤ), ((N - i : ℕ) : ℤ))) -
          gtop (((i : ℕ) : ℝ≥0), ((N - i : ℕ) : ℝ≥0)) ≤ D N ω) ∧
      (∀ N : ℕ, Integrable (D N) (environmentLaw ν)) ∧
      Tendsto (fun N : ℕ => (∫ ω, D N ω ∂environmentLaw ν) / N) atTop (𝓝 0) := by
  classical
  let χ : ℝ → ℝ := fun t => if t = 1 then (1 : ℝ) else 0
  have hχ : Measurable χ :=
    Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const
  have hfield : Measurable (fun ω : Environment => fun z : Lattice => χ (ω z)) :=
    measurable_coordinatewise_environment_map χ hχ
  have hlaw := environmentLaw_map_coordinatewise ν χ hχ
  have : IsProbabilityMeasure (ν.map χ) :=
    (Measure.isProbabilityMeasure_map_iff hχ.aemeasurable).2 inferInstance
  have hν : ∀ᵐ t ∂ν.map χ, 0 ≤ t ∧ t ≤ 1 := by
    refine (ae_map_iff (p := fun y : ℝ => 0 ≤ y ∧ y ≤ 1) hχ.aemeasurable
      (by exact measurableSet_Icc)).2 (Eventually.of_forall fun t => ?_)
    by_cases ht : t = 1 <;> simp [χ, ht]
  obtain ⟨g', hg'⟩ := exists_shape_with_expected_bounds_of_ae_mem_unit_interval (ν.map χ) hν
  have hsample : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage (fun z => χ (ω z)) 0 d - g' ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ) := by
    have h := hg'.2.2.2.1
    rw [← hlaw] at h
    exact ae_of_ae_map hfield.aemeasurable h
  have hgg : gtop = g' := by
    obtain ⟨ω, h1, h2⟩ := (htshape.and hsample).exists
    refine shapeCandidates_eq_of_common_environment gtop g' htcont hg'.1 hthom hg'.2.1
      (topField ω) ?_ ?_
    · intro ε hε
      obtain ⟨N, _, hN⟩ := h1 ε hε
      exact ⟨N, hN⟩
    · intro ε hε
      obtain ⟨N, _, hN⟩ := h2 ε hε
      exact ⟨N, hN⟩
  subst hgg
  have hle : ∀ᵐ t ∂ν.map χ, t ≤ 1 := hν.mono fun t ht => ht.2
  have hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂ν.map χ) < ∞ := by
    refine ⟨2, one_lt_two, ?_⟩
    calc (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ (2 : ℝ)) ∂ν.map χ)
        = ∫⁻ _t, 0 ∂ν.map χ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hν] with t ht
          have h0 : max (-t) 0 = 0 := max_eq_right (by linarith [ht.1])
          rw [h0, Real.zero_rpow (by norm_num)]
          simp
      _ = 0 := lintegral_zero
      _ < ∞ := ENNReal.zero_lt_top
  let D : ℕ → Environment → ℝ := fun N ω =>
    ⨆ (k : Fin (C * N + 1)) (i : Fin (N + 1)),
      max (lastPassage ω (-(k : ℤ), (k : ℤ)) ((i : ℕ), N - i) - ω (-(k : ℤ), (k : ℤ)) +
        ω ((-(k : ℤ), (k : ℤ)) + (((i : ℕ) : ℤ), ((N - i : ℕ) : ℤ))) -
        gtop (((i : ℕ) : ℝ≥0), ((N - i : ℕ) : ℝ≥0))) 0
  have h7 : (∀ N : ℕ, Integrable (D N) (environmentLaw (ν.map χ))) ∧
      Tendsto (fun N : ℕ => (∫ ω, D N ω ∂environmentLaw (ν.map χ)) / N) atTop (𝓝 0) :=
    expected_max_positive_deviation_startSet (ν.map χ) hle hneg gtop htcont hthom htconc
      hg'.2.2.2.1 C
  have hint : ∀ N : ℕ, Integrable (D N)
      ((environmentLaw ν).map (fun ω : Environment => fun z : Lattice => χ (ω z))) := by
    intro N
    rw [hlaw]
    exact h7.1 N
  have hmean : ∀ N : ℕ, ∫ ω, D N (topField ω) ∂environmentLaw ν =
      ∫ η, D N η ∂environmentLaw (ν.map χ) := by
    intro N
    have heq := integral_map hfield.aemeasurable (hint N).aestronglyMeasurable
    rw [hlaw] at heq
    exact heq.symm
  refine ⟨fun N ω => D N (topField ω), ?_, ?_, ?_, ?_⟩
  · intro N ω
    exact le_ciSup_of_le (Set.finite_range _).bddAbove 0
      (le_ciSup_of_le (Set.finite_range _).bddAbove 0 (le_max_right _ _))
  · intro N ω k i
    exact le_ciSup_of_le (Set.finite_range _).bddAbove k
      (le_ciSup_of_le (Set.finite_range _).bddAbove i (le_max_left _ _))
  · intro N
    exact (hint N).comp_measurable hfield
  · refine h7.2.congr (fun N => ?_)
    exact congrArg (fun s => s / (N : ℝ)) (hmean N).symm

/-- Some environment has a nonempty reached set, a half-line edge close to the speed `β`,
and a small deviation. -/
private theorem exists_good_environment (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (β : ℝ)
    (hβ : IsGLB (Set.range fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)) β)
    (η : ℝ) (hη : 0 < η) (ε : ℝ) (hε : 0 < ε)
    (D : ℕ → Environment → ℝ) (hD0 : ∀ N ω, 0 ≤ D N ω)
    (hDint : ∀ N, Integrable (D N) (environmentLaw ν))
    (hDtend : Tendsto (fun N : ℕ => (∫ ω, D N ω ∂environmentLaw ν) / N) atTop (𝓝 0)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ ω : Environment,
      (openReachSet (topSites ω) antidiagHalfLine N).Nonempty ∧
      (N : ℝ) - halfLineEdge ω N ≤ (1 - β + η) * N ∧ D N ω ≤ ε * N := by
  have hdef : ∀ n : ℕ, ∫ ω, ((n + 1 : ℕ) : ℝ) - (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν ≤
      (1 - β) * ((n : ℝ) + 1) := by
    intro n
    have h1 : β ≤ (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1) :=
      hβ.1 (Set.mem_range_self n)
    have h2 : β * ((n : ℝ) + 1) ≤ ∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).1 h1
    rw [integral_sub (integrable_const _) (integrable_halfLineEdge ν hp₀ (n + 1))]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    push_cast
    linarith
  have hdefN : ∀ N : ℕ, 1 ≤ N →
      ∫ ω, (N : ℝ) - (halfLineEdge ω N : ℝ) ∂environmentLaw ν ≤ (1 - β) * N := by
    intro N hN
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have h := hdef n
    push_cast at h ⊢
    exact h
  have hY0 : ∀ (N : ℕ) (ω : Environment), 0 ≤ (N : ℝ) - (halfLineEdge ω N : ℝ) := by
    intro N ω
    have h : (halfLineEdge ω N : ℝ) ≤ N := by exact_mod_cast halfLineEdge_le ω N
    linarith
  have hYint : ∀ N : ℕ, Integrable (fun ω => (N : ℝ) - (halfLineEdge ω N : ℝ)) (environmentLaw ν) :=
    fun N => (integrable_const _).sub (integrable_halfLineEdge ν hp₀ N)
  have hβ1 : β ≤ 1 := by
    have h := hdefN 1 le_rfl
    have h0 : 0 ≤ ∫ ω, ((1 : ℕ) : ℝ) - (halfLineEdge ω 1 : ℝ) ∂environmentLaw ν :=
      integral_nonneg (fun ω => hY0 1 ω)
    simp only [Nat.cast_one, mul_one] at h h0
    linarith
  set t : ℝ := 1 - β + η with ht
  have htpos : 0 < t := by rw [ht]; linarith
  have hedge : ∀ N : ℕ, 1 ≤ N →
      (environmentLaw ν).real {ω | t * N ≤ (N : ℝ) - (halfLineEdge ω N : ℝ)} ≤ (1 - β) / t := by
    intro N hN
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := environmentLaw ν)
      (f := fun ω => (N : ℝ) - (halfLineEdge ω N : ℝ))
      (Eventually.of_forall (hY0 N)) (hYint N) (t * N)
    have h2 := hdefN N hN
    rw [le_div_iff₀ htpos]
    by_contra hc
    have hc' := not_le.1 hc
    nlinarith [mul_pos hNpos (sub_pos.2 hc')]
  have hDm : ∀ N : ℕ, (ε * N) * (environmentLaw ν).real {ω | ε * N ≤ D N ω} ≤ ∫ ω, D N ω ∂environmentLaw ν := fun N =>
    mul_meas_ge_le_integral_of_nonneg (μ := environmentLaw ν) (f := D N)
      (Eventually.of_forall (hD0 N)) (hDint N) _
  have hpos : 0 < ε * (η / t) := by positivity
  obtain ⟨N, hNev, hN1⟩ :=
    ((hDtend.eventually (gt_mem_nhds hpos)).and (eventually_ge_atTop 1)).exists
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN1
  have hint_lt : ∫ ω, D N ω ∂environmentLaw ν < ε * (η / t) * N := by
    have hNev' : (∫ ω, D N ω ∂environmentLaw ν) / (N : ℝ) < ε * (η / t) := hNev
    rwa [div_lt_iff₀ hNpos] at hNev'
  have hm2 : (environmentLaw ν).real {ω | ε * N ≤ D N ω} < η / t := by
    have hm := hDm N
    by_contra hc
    have hc' := not_lt.1 hc
    nlinarith [mul_le_mul_of_nonneg_left hc' (mul_pos hε hNpos).le]
  have hnull : environmentLaw ν {ω | ¬ ∀ n : ℕ, (openReachSet (topSites ω) antidiagHalfLine n).Infinite} = 0 :=
    ae_iff.1 (ae_openReachSet_halfLine_infinite ν hp₀)
  set S1 : Set Environment := {ω | t * N ≤ (N : ℝ) - (halfLineEdge ω N : ℝ)}
  set S2 : Set Environment := {ω | ε * N ≤ D N ω}
  set Z : Set Environment :=
    {ω | ¬ ∀ n : ℕ, (openReachSet (topSites ω) antidiagHalfLine n).Infinite}
  have hex : ∃ ω : Environment, ω ∉ (S1 ∪ S2) ∪ Z := by
    by_contra hcon
    have hsub : (Set.univ : Set Environment) ⊆ (S1 ∪ S2) ∪ Z :=
      fun ω _ => Classical.byContradiction fun h => hcon ⟨ω, h⟩
    have h1 := measureReal_mono (μ := environmentLaw ν) hsub
    have h2a := measureReal_union_le (μ := environmentLaw ν) (S1 ∪ S2) Z
    have h2b := measureReal_union_le (μ := environmentLaw ν) S1 S2
    have hZ : (environmentLaw ν).real Z = 0 := by
      rw [measureReal_def, (hnull : environmentLaw ν Z = 0)]
      simp
    rw [probReal_univ] at h1
    have h3 : (environmentLaw ν).real S1 ≤ (1 - β) / t := hedge N hN1
    have h5 : (environmentLaw ν).real S2 < η / t := hm2
    have h4 : (1 - β) / t + η / t = 1 := by
      field_simp
      linarith [ht]
    linarith
  obtain ⟨ω, hω⟩ := hex
  have a1 : ω ∉ S1 := fun h => hω (Set.mem_union_left _ (Set.mem_union_left _ h))
  have a2 : ω ∉ S2 := fun h => hω (Set.mem_union_left _ (Set.mem_union_right _ h))
  have a3 : ω ∉ Z := fun h => hω (Set.mem_union_right _ h)
  refine ⟨N, hN1, ω, ?_, ?_, ?_⟩
  · have h : ∀ n : ℕ, (openReachSet (topSites ω) antidiagHalfLine n).Infinite := not_not.1 a3
    exact (h N).nonempty
  · have h : ¬ (t * N ≤ (N : ℝ) - (halfLineEdge ω N : ℝ)) := a1
    exact (not_le.1 h).le
  · have h : ¬ (ε * N ≤ D N ω) := a2
    exact (not_le.1 h).le

/-- A limit point argument: approximate points with value close to `1` and first coordinate
close to `β` give a point with value exactly `1` and first coordinate at least `β`. -/
private theorem exists_limit_point (β : ℝ) (F : ℝ → ℝ) (hF : Continuous F)
    (hle : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → F x ≤ 1)
    (key : ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε →
      ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ β - η ≤ x ∧ 1 - ε ≤ F x) :
    ∃ x : ℝ, 0 ≤ x ∧ β ≤ x ∧ x ≤ 1 ∧ F x = 1 := by
  choose x hx0 hx1 hxβ hxF using fun m : ℕ =>
    key (1 / ((m : ℝ) + 1)) (by positivity) (1 / ((m : ℝ) + 1)) (by positivity)
  obtain ⟨a, haI, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq
    (x := x) (s := Set.Icc (0 : ℝ) 1) (fun m => ⟨hx0 m, hx1 m⟩)
  have hz : Tendsto (fun m : ℕ => 1 / ((φ m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hβa : β ≤ a := by
    have h1 : Tendsto (fun m : ℕ => β - 1 / ((φ m : ℝ) + 1)) atTop (𝓝 β) := by
      simpa using (tendsto_const_nhds (x := β)).sub hz
    exact le_of_tendsto_of_tendsto' h1 hlim (fun m => hxβ (φ m))
  have hFa : 1 ≤ F a := by
    have h1 : Tendsto (fun m : ℕ => 1 - 1 / ((φ m : ℝ) + 1)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hz
    exact le_of_tendsto_of_tendsto' h1 ((hF.tendsto a).comp hlim) (fun m => hxF (φ m))
  exact ⟨a, haI.1, hβa, haI.2, le_antisymm (hle a haI.1 haI.2) hFa⟩

/-- Beyond the edge speed there is a direction where the top-field shape equals `1`. -/
theorem exists_gtop_eq_one_ge_edgeSpeed (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (hp₁ : ν {1} < 1)
    (gtop : Quadrant → ℝ) (htcont : Continuous gtop)
    (hthom : ∀ (c : ℝ≥0) (x : Quadrant), gtop (c * x.1, c * x.2) = (c : ℝ) * gtop x)
    (htconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * gtop x + (t : ℝ) * gtop y ≤ gtop (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (htshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage (topField ω) 0 d - gtop ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (β : ℝ)
    (hβ : IsGLB (Set.range fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)) β) :
    ∃ x : ℝ, 0 ≤ x ∧ β ≤ x ∧ x ≤ 1 ∧ gtop (toQuadrant (x, 1 - x)) = 1 := by
  have _hp₁ := hp₁
  have hq : Continuous fun x : ℝ => toQuadrant (x, 1 - x) :=
    (continuous_real_toNNReal.comp continuous_id).prodMk
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))
  have hF : Continuous fun x : ℝ => gtop (toQuadrant (x, 1 - x)) := htcont.comp hq
  have hle : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → gtop (toQuadrant (x, 1 - x)) ≤ 1 := by
    intro x hx0 hx1
    have h := ((expected_floor_limit_of_top_shape_block ν gtop htcont hthom htconc
      htshape).2.2.1 (toQuadrant (x, 1 - x))).2
    have h1 : ((toQuadrant (x, 1 - x)).1 : ℝ) + (toQuadrant (x, 1 - x)).2 = 1 := by
      simp [toQuadrant, Real.coe_toNNReal _ hx0, Real.coe_toNNReal _ (sub_nonneg.2 hx1)]
    linarith
  refine exists_limit_point β _ hF hle ?_
  intro η hη ε hε
  obtain ⟨D, hD0, hDle, hDint, hDtend⟩ :=
    exists_top_deviation ν gtop htcont hthom htconc htshape ⌈1 - β + η⌉₊
  obtain ⟨N, hN1, ω, hne, hedge, hDω⟩ :=
    exists_good_environment ν hp₀ β hβ η hη ε hε D hD0 hDint hDtend
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN1
  have hC : 1 - β + η ≤ (⌈1 - β + η⌉₊ : ℝ) := Nat.le_ceil _
  have hk : (N : ℤ) - halfLineEdge ω N ≤ ((⌈1 - β + η⌉₊ : ℕ) : ℤ) * N := by
    have h : (N : ℝ) - halfLineEdge ω N ≤ (⌈1 - β + η⌉₊ : ℝ) * N :=
      hedge.trans (mul_le_mul_of_nonneg_right hC hNpos.le)
    exact_mod_cast h
  obtain ⟨i, hiN, hai, hg⟩ := exists_direction_of_edge gtop ω N ⌈1 - β + η⌉₊ hne hk (D N ω)
    (fun k i => hDle N ω k i)
  have hiN' : (i : ℝ) ≤ N := by exact_mod_cast hiN
  have hx0 : 0 ≤ (i : ℝ) / N := by positivity
  have hx1 : (i : ℝ) / N ≤ 1 := (div_le_one hNpos).2 hiN'
  refine ⟨(i : ℝ) / N, hx0, hx1, ?_, ?_⟩
  · rw [le_div_iff₀ hNpos]
    nlinarith
  · have e1 : (N : ℝ≥0) * ((i : ℝ) / N).toNNReal = (i : ℝ≥0) := by
      apply NNReal.eq
      simp only [NNReal.coe_mul, NNReal.coe_natCast, Real.coe_toNNReal _ hx0]
      field_simp
    have e2 : (N : ℝ≥0) * (1 - (i : ℝ) / N).toNNReal = ((N - i : ℕ) : ℝ≥0) := by
      apply NNReal.eq
      simp only [NNReal.coe_mul, NNReal.coe_natCast, Real.coe_toNNReal _ (sub_nonneg.2 hx1),
        Nat.cast_sub hiN]
      field_simp
    have hh := hthom (N : ℝ≥0) (toQuadrant ((i : ℝ) / N, 1 - (i : ℝ) / N))
    change gtop ((N : ℝ≥0) * ((i : ℝ) / N).toNNReal,
      (N : ℝ≥0) * (1 - (i : ℝ) / N).toNNReal) = _ at hh
    rw [e1, e2] at hh
    have hNN : ((N : ℝ≥0) : ℝ) = N := NNReal.coe_natCast N
    rw [hNN] at hh
    show 1 - ε ≤ gtop (toQuadrant ((i : ℝ) / N, 1 - (i : ℝ) / N))
    nlinarith
end LPPDifferentiability
