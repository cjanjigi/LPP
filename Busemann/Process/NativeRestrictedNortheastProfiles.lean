/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RestrictedNortheastProfiles
public import Busemann.Process.NativeCocycleAllStarts
public import Busemann.Process.NativeExtremeDriftPinning
import Busemann.Process.RealShortWeightWindows
import Busemann.Process.ShellComparisonBounds
import LPP_Foundations.Analysis.AbsoluteMomentShape
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import Martin2004.Shape.ExpectedRateUniform
import LPP_Foundations.Model.LastPassage.UniformShapeAllStarts
import Mathlib.Tactic

/-! The native paired restricted northeast variational limits. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal NNReal BigOperators Topology

namespace LPP.Busemann

/-- Both selected-last-step northeast passage values have the closed-segment
variational limits in GRS arXiv:1510.00859v2, Lemma 6.4, (6.9)–(6.10),
as used in JR arXiv:1810.03580v3, Theorem 4.16. One event covers all fixed
signed starts, limiting unit directions and cofinal positive-coordinate sequences. -/
theorem ae_native_restrictedNE_shape_profiles
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (hnonconstant : ¬ ∃ c : ℝ, ∀ᵐ t ∂μ, t = c)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P)
    (hRec : recovers_weight_map_ae P processEnvironment B)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g)
    (η : InteriorDirection) (h : SupportTilt g)
    (hh : SupportsAt g η h.1)
    (hext : (∀ k : SupportTilt g,
      SupportsAt g η k.1 → h.1.1 ≤ k.1.1) ∨
      (∀ k : SupportTilt g,
        SupportsAt g η k.1 → k.1.1 ≤ h.1.1))
    (hMean : ∀ i : Fin 2,
      (∫ q, B 0 (finiteEdgeStep i) q ∂P) =
        -finiteTiltCoordinate h.1 i) :
    ∀ᵐ q ∂P, ∀ (x : Lattice) (ξ : Quadrant)
      (hξunit : (ξ.1 : ℝ) + (ξ.2 : ℝ) = 1)
      (d : ℕ → ℕ × ℕ),
      (hpositive : ∀ n : ℕ, 0 < (d n).1 ∧ 0 < (d n).2) →
      Tendsto (fun n => (d n).1 + (d n).2) atTop atTop →
      Tendsto (fun n =>
        ((d n).1 : ℝ) / (((d n).1 + (d n).2 : ℕ) : ℝ))
        atTop (𝓝 (ξ.1 : ℝ)) →
      let H : ℝ := sSup ((fun τ : ℝ =>
        g (Real.toNNReal ((ξ.1 : ℝ) - τ), ξ.2) -
          h.1.1 * τ) '' Set.Icc 0 (ξ.1 : ℝ))
      let V : ℝ := sSup ((fun τ : ℝ =>
        g (ξ.1, Real.toNNReal ((ξ.2 : ℝ) - τ)) -
          h.1.2 * τ) '' Set.Icc 0 (ξ.2 : ℝ))
      Tendsto (fun n =>
        restrictedNE (processEnvironment q)
          (fun a b => B a b q) x (d n) 0
          (by simpa using (hpositive n).1) /
          (((d n).1 + (d n).2 : ℕ) : ℝ)) atTop (𝓝 H) ∧
      Tendsto (fun n =>
        restrictedNE (processEnvironment q)
          (fun a b => B a b q) x (d n) 1
          (by simpa using (hpositive n).2) /
          (((d n).1 + (d n).2 : ℕ) : ℝ)) atTop (𝓝 V) := by
  classical
  have _hNonconstant := hnonconstant
  have hGeometry := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  obtain ⟨p, hp, hmomentp⟩ := hmoment
  have hPositive := ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
    μ hp hmomentp
  have hNegative := ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment
    μ hp hmomentp
  obtain ⟨_, _, hOrigin⟩ := ae_uniform_of_isExpectedRateShape μ hNegative hPositive.2 hg
  have hAllStarts := LPP.ae_uniform_passage_shape_all_starts_of_origin μ g hOrigin
  have hProjection : MeasurePreserving processEnvironment P (environmentLaw μ) :=
    ⟨measurable_fst, hMarginal⟩
  have hOrdinary := hProjection.quasiMeasurePreserving.ae hAllStarts
  let mProc : MeasurableSpace ProcessSample := inferInstance
  let I : MeasurableSpace ProcessSample :=
    ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
  let : MeasurableSpace ProcessSample := mProc
  let u : Fin 2 → ProcessSample → ℝ := fun i => P[B 0 (finiteEdgeStep i) | I]
  let Δ : ℕ → Finset Lattice := fun m => insert 0
    (((Finset.Icc (0 : ℤ) (m : ℤ)).product
      (Finset.Icc (0 : ℤ) (m : ℤ))).filter
        (fun z => z.1 + z.2 ≤ (m : ℤ)))
  have hTriangle := ae_uniform_recovering_cocycle_triangle_shape_all_starts
    μ ⟨p, hp, hmomentp⟩ P hMarginal hShift B hB hInt hRec
  change ∀ᵐ q ∂P, ∀ x : Lattice, Tendsto (fun m : ℕ =>
    (Δ m).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
      (fun z => |B x (x + z) q -
        (u 0 q * (z.1 : ℝ) + u 1 q * (z.2 : ℝ))|) / (m : ℝ))
    atTop (𝓝 0) at hTriangle
  have hPinned := ae_canonical_drift_pinned_at_extreme_support
    μ ⟨p, hp, hmomentp⟩ P hMarginal hShift B hB hInt hRec g hg η h hh hext hMean
  change ∀ᵐ q ∂P, SupportsAt g η (-u 0 q, -u 1 q) ∧
    ∀ i : Fin 2, u i q = -finiteTiltCoordinate h.1 i at hPinned
  let ball : ℕ → Finset Lattice := fun m => insert 0
    (((Finset.Icc (-(2 * (m : ℤ))) (2 * (m : ℤ))).product
      (Finset.Icc (-(2 * (m : ℤ))) (2 * (m : ℤ)))).filter
        (fun z => z.1.natAbs + z.2.natAbs ≤ 2 * m))
  have hShort := ae_eventually_small_real_short_weight_windows μ ⟨p, hp, hmomentp⟩ P hMarginal
  -- All stochastic inputs are fixed before the arbitrary direction and sequence.
  filter_upwards [hOrdinary, hTriangle, hPinned, hShort, hB.2.2]
    with q hordinary htriangle hpinned hshort hadd
  have hu0 : u 0 q = -h.1.1 := by
    simpa only [finiteTiltCoordinate, Fin.val_zero, ite_true] using hpinned.2 0
  have hu1 : u 1 q = -h.1.2 := by
    simpa only [finiteTiltCoordinate, Fin.val_one, one_ne_zero, ite_false] using hpinned.2 1
  let W : Fin 2 → ℝ → ℕ → ℝ := fun i δ m =>
    (ball m).sup' (by dsimp [ball]; exact Finset.insert_nonempty _ _)
      (fun z => (∑ k ∈ Finset.range (⌊(m : ℝ) * δ⌋₊ + 1),
        |processEnvironment q (z + (k : ℤ) • finiteEdgeStep i)|) / (m : ℝ))
  change ∀ ε : ℝ, 0 < ε → ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ i : Fin 2,
      ∀ᶠ m : ℕ in atTop, W i δ m < 2 * ε at hshort
  intro x ξ hξunit d hpositive hsize hratio
  have hPass := uniform_passage_error_on_triangles (processEnvironment q) g x (hordinary x)
  -- The actual canonical drift remains conditional until this extreme pinning.
  have hCoc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∀ e : ℕ × ℕ, e.1 + e.2 ≤ m →
        |B x (x + ((e.1 : ℤ), (e.2 : ℤ))) q -
          ((-h.1.1) * (e.1 : ℝ) + (-h.1.2) * (e.2 : ℝ))| ≤ ε * (m : ℝ) := by
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((htriangle x).eventually (gt_mem_nhds hε))
    refine ⟨max 1 N, ?_⟩
    intro m hm e he
    have hmpos : 0 < m := by omega
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
    have hemem : ((e.1 : ℤ), (e.2 : ℤ)) ∈ Δ m := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, ?_⟩
      dsimp
      omega
    have hpoint := Finset.le_sup'
      (fun z : Lattice => |B x (x + z) q -
        (u 0 q * (z.1 : ℝ) + u 1 q * (z.2 : ℝ))|) hemem
    have hbound := (div_lt_iff₀ hmR).mp (hN m (by omega))
    rw [hu0, hu1] at hpoint hbound
    have hsmall := hpoint.trans_lt hbound
    exact le_of_lt (by simpa only [Int.cast_natCast] using hsmall)
  -- The zero-index term of one inclusive short window bounds every moving site.
  have hWeight : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∀ e : ℕ × ℕ, e.1 + e.2 ≤ m →
        |processEnvironment q (x + ((e.1 : ℤ), (e.2 : ℤ)))| ≤ ε * (m : ℝ) := by
    intro ε hε
    obtain ⟨δ, hδ, _, hδbound⟩ := hshort (ε / 2) (by positivity)
    have hevent := hδbound δ hδ le_rfl 0
    obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
    refine ⟨max 1 (max N (x.1.natAbs + x.2.natAbs)), ?_⟩
    intro m hm e he
    have hmpos : 0 < m := by omega
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
    let z : Lattice := x + ((e.1 : ℤ), (e.2 : ℤ))
    have hnorm1 : z.1.natAbs ≤ x.1.natAbs + e.1 := by
      simpa only [z, Prod.fst_add, Int.natAbs_natCast] using
        Int.natAbs_add_le x.1 (e.1 : ℤ)
    have hnorm2 : z.2.natAbs ≤ x.2.natAbs + e.2 := by
      simpa only [z, Prod.snd_add, Int.natAbs_natCast] using
        Int.natAbs_add_le x.2 (e.2 : ℤ)
    have hzball : z ∈ ball m := (signed_ball_mem m z).mpr (by omega)
    have hzero : (0 : ℕ) ∈ Finset.range (⌊(m : ℝ) * δ⌋₊ + 1) := by simp
    have hsum := Finset.single_le_sum
      (fun k (_ : k ∈ Finset.range (⌊(m : ℝ) * δ⌋₊ + 1)) =>
        abs_nonneg (processEnvironment q (z + (k : ℤ) • finiteEdgeStep 0))) hzero
    have hsingle : |processEnvironment q z| ≤
        ∑ k ∈ Finset.range (⌊(m : ℝ) * δ⌋₊ + 1),
          |processEnvironment q (z + (k : ℤ) • finiteEdgeStep 0)| := by
      simpa only [Nat.cast_zero, zero_zsmul, add_zero] using hsum
    have hmaximum := Finset.le_sup'
      (fun z => (∑ k ∈ Finset.range (⌊(m : ℝ) * δ⌋₊ + 1),
        |processEnvironment q (z + (k : ℤ) • finiteEdgeStep 0)|) / (m : ℝ)) hzball
    have hpoint : |processEnvironment q z| / (m : ℝ) ≤ W 0 δ m :=
      (div_le_div_of_nonneg_right hsingle hmR.le).trans hmaximum
    have hsmall : |processEnvironment q z| / (m : ℝ) < ε := by
      have hb := hpoint.trans_lt (hN m (by omega))
      linarith only [hb]
    exact le_of_lt ((div_lt_iff₀ hmR).mp hsmall)
  let m : ℕ → ℝ := fun n => ((d n).1 + (d n).2 : ℕ)
  let north : ℕ → ℝ := fun n =>
    (Finset.Icc 1 (d n).1).sup' (Finset.nonempty_Icc.mpr (hpositive n).1)
      (fun ℓ => g (Real.toNNReal (((((d n).1 - ℓ : ℕ) : ℝ)) / m n),
        Real.toNNReal (((((d n).2 - 1 : ℕ) : ℝ)) / m n)) + (-h.1.1) * ℓ / m n)
  let east : ℕ → ℝ := fun n =>
    (Finset.Icc 1 (d n).2).sup' (Finset.nonempty_Icc.mpr (hpositive n).2)
      (fun ℓ => g (Real.toNNReal (((((d n).1 - 1 : ℕ) : ℝ)) / m n),
        Real.toNNReal (((((d n).2 - ℓ : ℕ) : ℝ)) / m n)) + (-h.1.2) * ℓ / m n)
  let rN : ℕ → ℝ := fun n => restrictedNE (processEnvironment q)
    (fun a b => B a b q) x (d n) 0 (by simpa using (hpositive n).1) / m n
  let rE : ℕ → ℝ := fun n => restrictedNE (processEnvironment q)
    (fun a b => B a b q) x (d n) 1 (by simpa using (hpositive n).2) / m n
  have hErrors : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      |rN n - north n| ≤ 4 * ε ∧ |rE n - east n| ≤ 4 * ε := by
    intro ε hε
    obtain ⟨NP, hNP⟩ := hPass ε hε
    obtain ⟨NC, hNC⟩ := hCoc ε hε
    obtain ⟨NW, hNW⟩ := hWeight ε hε
    filter_upwards [hsize.eventually (eventually_ge_atTop (max NP (max NC NW)))] with n hn
    exact restrictedNE_grid_error (processEnvironment q) (fun a b => B a b q) hadd
      g hGeometry.2.1 x (d n) (hpositive n).1 (hpositive n).2 (-h.1.1) (-h.1.2) ε
      (hNP _ (by omega)) (hNC _ (by omega)) (hNW _ (by omega))
  have hApproxNorth : Tendsto (fun n => rN n - north n) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hErrors (ε / 8) (by positivity)] with n hn
    rw [Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt hn.1 (by linarith only [hε])
  have hApproxEast : Tendsto (fun n => rE n - east n) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hErrors (ε / 8) (by positivity)] with n hn
    rw [Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt hn.2 (by linarith only [hε])
  have hNorth := ProbabilityBasics.tendsto_segment_grid_maximum
    g hGeometry.1 (-h.1.1) ξ hξunit d hpositive hsize hratio
  have hNorthGrid : Tendsto north atTop (𝓝 (sSup ((fun τ : ℝ =>
      g (Real.toNNReal ((ξ.1 : ℝ) - τ), ξ.2) - h.1.1 * τ) '' Set.Icc 0 (ξ.1 : ℝ)))) := by
    simpa only [north, m, neg_mul, sub_eq_add_neg] using hNorth
  -- East uses the same events and the explicitly transposed deterministic grid.
  have hmpos (n : ℕ) : 0 < m n := by
    have hp := (hpositive n).1
    dsimp [m]
    exact_mod_cast (show 0 < (d n).1 + (d n).2 by omega)
  have hratioEq (n : ℕ) : ((d n).2 : ℝ) / m n = 1 - ((d n).1 : ℝ) / m n := by
    have hsum : ((d n).1 : ℝ) + (d n).2 = m n := by simp only [m, Nat.cast_add]
    field_simp [(hmpos n).ne']
    linarith only [hsum]
  have hξsecond : 1 - (ξ.1 : ℝ) = (ξ.2 : ℝ) := by linarith only [hξunit]
  have hratioFirst : Tendsto (fun n => ((d n).1 : ℝ) / m n)
      atTop (𝓝 (ξ.1 : ℝ)) := hratio
  have hratioEast : Tendsto (fun n => ((d n).2 : ℝ) / m n) atTop (𝓝 (ξ.2 : ℝ)) := by
    simpa only [← hratioEq, hξsecond] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub hratioFirst
  have hEast := ProbabilityBasics.tendsto_segment_grid_maximum
    (fun z => g z.swap) (hGeometry.1.comp continuous_swap) (-h.1.2) ξ.swap
    (by simpa only [Prod.swap, add_comm] using hξunit)
    (fun n => (d n).swap) (fun n => ⟨(hpositive n).2, (hpositive n).1⟩)
    (by simpa only [Prod.swap, Nat.add_comm] using hsize)
    (by simpa only [Prod.swap, m, Nat.add_comm] using hratioEast)
  have hEastGrid : Tendsto east atTop (𝓝 (sSup ((fun τ : ℝ =>
      g (ξ.1, Real.toNNReal ((ξ.2 : ℝ) - τ)) - h.1.2 * τ) '' Set.Icc 0 (ξ.2 : ℝ)))) := by
    simpa only [east, m, Prod.swap, Nat.add_comm, neg_mul, sub_eq_add_neg] using hEast
  constructor
  · simpa only [sub_add_cancel, zero_add] using hApproxNorth.add hNorthGrid
  · simpa only [sub_add_cancel, zero_add] using hApproxEast.add hEastGrid

end LPP.Busemann
