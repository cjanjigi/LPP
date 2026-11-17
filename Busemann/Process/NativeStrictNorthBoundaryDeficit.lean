/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.NorthBoundaryExitFormula
public import Busemann.Process.NativeCalibratedConfinement
import Busemann.Process.NativeRestrictedNortheastProfiles
import Busemann.Geometry.RestrictedProfileComparison
import ProbabilityBasics.Analysis.CompactSubsequenceEventual
import LPP_Foundations.Analysis.AbsoluteMomentShape
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import ProbabilityBasics.Probability.AbsoluteMomentTail
import Martin2004.Shape.ExpectedRateAllStarts
import Busemann.Geometry.SupportIdentities
import Mathlib.Tactic

/-! Restricted-profile comparison on the north boundary, uniformly in an endpoint cone. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal NNReal Topology

namespace LPP.Busemann

/-- The one-sided north value is strictly below the recovering cocycle outside
its whole single-tilt contact face. The proof uses the actual paired restricted
limits and derivative-derived class preference in GRS arXiv:1510.00859v2,
Lemma 6.5 and Theorem 6.1 Step 1, with compact cone and exact-axis details. -/
theorem ae_native_strict_north_boundary_deficit
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
      (∫ s, B 0 (finiteEdgeStep i) s ∂P) =
        -finiteTiltCoordinate h.1 i)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hθface : ∀ ζ ∈ supportFace g h, θ < (ζ.1.1 : ℝ)) :
    ∀ᵐ s ∂P, ∀ x : Lattice, ∀ d : ℕ → ℕ × ℕ,
      (∀ n, (d n).1 + (d n).2 = n) →
      (∀ᶠ n : ℕ in atTop, ((d n).1 : ℝ) / (n : ℝ) ≤ θ) →
      ∀ᶠ n : ℕ in atTop, 0 < n ∧
        (let v : Lattice :=
           x + (((d n).1 : ℤ), ((d n).2 : ℤ))
         let N : Environment := fun z =>
           if z.2 = v.2 ∧ z.1 < v.1 then
             B z (z + (1, 0)) s
           else processEnvironment s z
         lastPassage N x (d n) < B x v s) := by
  classical
  have _hConeEndpoint : (0 : ℝ) ∈ Set.Icc 0 θ := ⟨le_refl 0, hθ0⟩
  -- The contact interval belongs to this one support tilt.
  have hGeometry := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  have hHom (c : ℝ≥0) (z : Quadrant) : g (c • z) = (c : ℝ) * g z := by
    change g (c * z.1, c * z.2) = (c : ℝ) * g z
    exact hGeometry.2.1 c z
  have hConc (a b : Quadrant) (r s : ℝ≥0) (hrs : r + s = 1) :
      (r : ℝ) * g a + (s : ℝ) * g b ≤ g (r • a + s • b) := by
    change (r : ℝ) * g a + (s : ℝ) * g b ≤
      g (r * a.1 + s * b.1, r * a.2 + s * b.2)
    exact hGeometry.2.2 a b r s hrs
  have hGaps := support_tilt_strict_axis_gaps_of_absolute_moment μ hmoment hnonconstant g hg h
  obtain ⟨left, right, hLeft, hRight, _, _, hContact⟩ :=
    exists_support_face_interval_with_contact_characterization
      g hGeometry.1 hConc hHom h hGaps.1 hGaps.2
  obtain ⟨ζ, hζ⟩ := h.2
  have hMajorant := ((supportsAt_iff_through_origin_majorant_and_contact g ζ h.1 hHom).mp hζ).1
  have hConeSep : θ < (left.1.1 : ℝ) :=
    hθface left hLeft
  have hProfiles := ae_native_restrictedNE_shape_profiles
    μ hmoment hnonconstant P hMarginal hShift B hB hInt hRec g hg η h hh hext hMean
  obtain ⟨p, hp, hmomentp⟩ := hmoment
  have hPositive := ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment μ hp hmomentp
  have hNegative := ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment μ hp hmomentp
  have hProjection : MeasurePreserving processEnvironment P (environmentLaw μ) := ⟨measurable_fst, hMarginal⟩
  have hOrdinary := hProjection.quasiMeasurePreserving.ae
    (LPP.ae_normalized_passage_shape_all_starts μ hNegative hPositive.2 g hg)
  let mProc : MeasurableSpace ProcessSample := inferInstance
  let I : MeasurableSpace ProcessSample :=
    ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
  let : MeasurableSpace ProcessSample := mProc
  let u : Fin 2 → ProcessSample → ℝ := fun i => P[B 0 (finiteEdgeStep i) | I]
  let Δ : ℕ → Finset Lattice := fun n => insert 0
    (((Finset.Icc (0 : ℤ) (n : ℤ)).product (Finset.Icc (0 : ℤ) (n : ℤ))).filter
      (fun z => z.1 + z.2 ≤ (n : ℤ)))
  have hTriangle := ae_uniform_recovering_cocycle_triangle_shape_all_starts
    μ ⟨p, hp, hmomentp⟩ P hMarginal hShift B hB hInt hRec
  change ∀ᵐ s ∂P, ∀ x : Lattice, Tendsto (fun n : ℕ =>
    (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
      (fun z => |B x (x + z) s - (u 0 s * (z.1 : ℝ) + u 1 s * (z.2 : ℝ))|) /
        (n : ℝ)) atTop (𝓝 0) at hTriangle
  have hPinned := ae_canonical_drift_pinned_at_extreme_support
    μ ⟨p, hp, hmomentp⟩ P hMarginal hShift B hB hInt hRec g hg η h hh hext hMean
  change ∀ᵐ s ∂P, SupportsAt g η (-u 0 s, -u 1 s) ∧
    ∀ i : Fin 2, u i s = -finiteTiltCoordinate h.1 i at hPinned
  -- One event is fixed before every signed start and oscillating endpoint sequence.
  filter_upwards [hProfiles, hOrdinary, hTriangle, hPinned, hB.2.2, hRec]
    with s hprofiles hs ht hpin ha hr
  intro x d hlen hratio
  have hu0 : u 0 s = -h.1.1 := by
    simpa only [finiteTiltCoordinate, Fin.val_zero, ite_true] using hpin.2 0
  have hu1 : u 1 s = -h.1.2 := by
    simpa only [finiteTiltCoordinate, Fin.val_one, one_ne_zero, ite_false] using hpin.2 1
  let q : ℝ → Quadrant := fun t => (Real.toNNReal t, Real.toNNReal (1 - t))
  have hContinuous : Continuous (fun t : ℝ => g (q t)) :=
    hGeometry.1.comp (continuous_real_toNNReal.prodMk
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_id)))
  -- Compose the normalized residual, rather than reproving ordinary shape.
  have hOrdinaryLimit (e : ℕ → ℕ × ℕ) (he : ∀ n, (e n).1 + (e n).2 = n)
      (φ : ℕ → ℕ) (hφ : StrictMono φ) (t : ℝ)
      (hlim : Tendsto (fun j => ((e (φ j)).1 : ℝ) / (φ j : ℝ)) atTop (𝓝 t)) :
      Tendsto (fun j => lastPassage (processEnvironment s) x (e (φ j)) / (φ j : ℝ))
        atTop (𝓝 (g (q t))) := by
    have hResidual := (hs x e he).comp hφ.tendsto_atTop
    have hShape := (hContinuous.tendsto t).comp hlim
    simpa only [Function.comp_def, q, sub_add_cancel, zero_add] using hResidual.add hShape
  let axis : ℕ → ℕ × ℕ := fun n => (0, n)
  have hAxisRatio : Tendsto (fun n => ((axis n).1 : ℝ) / (n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [axis, Nat.cast_zero, zero_div] using (tendsto_const_nhds (x := (0 : ℝ)))
  have hAxisOrdinary : Tendsto (fun n => lastPassage (processEnvironment s) x (axis n) / (n : ℝ))
      atTop (𝓝 (g (0, 1))) := by
    simpa only [q, sub_zero, Real.toNNReal_zero, Real.toNNReal_one] using
      hOrdinaryLimit axis (by intro n; simp only [axis, zero_add])
        (fun n : ℕ => n) strictMono_id 0 hAxisRatio
  -- The exact axis uses the actual full-invariant triangle estimate and pinning.
  have hAxisCocycle : Tendsto (fun n : ℕ => B x (x + ((0 : ℤ), (n : ℤ))) s / (n : ℝ))
      atTop (𝓝 (-h.1.2)) := by
    have hResidual : Tendsto (fun n : ℕ => B x (x + ((0 : ℤ), (n : ℤ))) s / (n : ℝ) - (-h.1.2))
        atTop (𝓝 0) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.mp ((ht x).eventually (gt_mem_nhds hε))
      refine ⟨max 1 N, ?_⟩
      intro n hn
      have hnpos : 0 < n := by omega
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
      have hmem : ((0 : ℤ), (n : ℤ)) ∈ Δ n := by
        apply Finset.mem_insert_of_mem
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, ?_⟩
        dsimp
        omega
      have hpoint := Finset.le_sup'
        (fun z : Lattice => |B x (x + z) s -
          (u 0 s * (z.1 : ℝ) + u 1 s * (z.2 : ℝ))|) hmem
      have hsmall := hN n (by omega)
      rw [hu0, hu1] at hpoint hsmall
      have hPoint : |B x (x + ((0 : ℤ), (n : ℤ))) s - (-h.1.2) * (n : ℝ)| ≤
          (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
            (fun z => |B x (x + z) s - ((-h.1.1) * (z.1 : ℝ) + (-h.1.2) * (z.2 : ℝ))|) := by
        simpa only [Int.cast_zero, Int.cast_natCast, mul_zero, zero_add] using hpoint
      have hdiv : B x (x + ((0 : ℤ), (n : ℤ))) s / (n : ℝ) - (-h.1.2) =
          (B x (x + ((0 : ℤ), (n : ℤ))) s - (-h.1.2) * (n : ℝ)) / (n : ℝ) := by
        field_simp [hnR.ne']
      rw [Real.dist_eq, sub_zero, hdiv, abs_div, abs_of_pos hnR]
      exact (div_le_div_of_nonneg_right hPoint hnR.le).trans_lt hsmall
    simpa only [sub_add_cancel, zero_add] using hResidual.add
      (tendsto_const_nhds (x := -h.1.2))
  have hAxisDeficit : ∀ᶠ n : ℕ in atTop, 0 < n ∧
      lastPassage (processEnvironment s) x (axis n) < B x (x + ((0 : ℤ), (n : ℤ))) s := by
    filter_upwards [hAxisOrdinary.eventually_lt hAxisCocycle hGaps.2,
      eventually_gt_atTop 0] with n hlt hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    exact ⟨hn, (div_lt_div_iff_of_pos_right hnR).mp hlt⟩
  let terminal : ℕ → Lattice := fun n => x + (((d n).1 : ℤ), ((d n).2 : ℤ))
  let field : ℕ → Environment := fun n z => if z.2 = (terminal n).2 ∧ z.1 < (terminal n).1 then B z (z + (1, 0)) s else processEnvironment s z
  let good : ℕ → Prop := fun n => 0 < n ∧ lastPassage (field n) x (d n) < B x (terminal n) s
  change ∀ᶠ n : ℕ in atTop, good n
  -- On this exact axis the modified boundary is unused. No restricted empty class occurs.
  have hAxisCut : ∀ᶠ n : ℕ in atTop, (d n).1 = 0 → good n := by
    filter_upwards [hAxisDeficit] with n hn
    intro hz
    have hdaxis : d n = axis n := by
      have hd := hlen n
      apply Prod.ext <;> dsimp only [axis] <;> omega
    have hfield : lastPassage (field n) x (d n) = lastPassage (processEnvironment s) x (axis n) := by
      rw [hdaxis, lastPassage_vertical, lastPassage_vertical]
      apply Finset.sum_congr rfl
      intro j _
      simp [field, terminal, hdaxis, axis]
    refine ⟨hn.1, ?_⟩
    rw [hfield]
    simpa only [terminal, hdaxis, axis, Nat.cast_zero] using hn.2
  have hSides : ∀ᶠ n : ℕ in atTop, 0 < n ∧ 0 < (d n).2 ∧
      ((d n).1 = 0 → good n) := by
    filter_upwards [hAxisCut, hratio, eventually_gt_atTop 0] with n haxis hc hn
    refine ⟨hn, ?_, haxis⟩
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    by_contra hnot
    have hz : (d n).2 = 0 := by omega
    have hfirst : (d n).1 = n := by have hd := hlen n; omega
    rw [hfirst, div_self hnR.ne'] at hc
    exact (not_lt_of_ge hc) hθ1
  let ratio : ℕ → ℝ := fun n => ((d n).1 : ℝ) / (n : ℝ)
  have hK : ∀ᶠ n : ℕ in atTop, ratio n ∈ Set.Icc 0 θ := by
    filter_upwards [hratio, eventually_gt_atTop 0] with n hc hn
    exact ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), hc⟩
  -- Compactness handles the original oscillating cone, not only direction limits.
  apply ProbabilityBasics.eventually_of_isSeqCompact (Set.Icc 0 θ) isCompact_Icc.isSeqCompact ratio hK good
  intro φ hφ t htCone hlim
  by_contra hnot
  have hcut := hφ.tendsto_atTop.eventually hSides
  obtain ⟨ψ, hψ, hbad⟩ := extraction_of_frequently_atTop
    ((Filter.not_eventually.mp hnot).and_eventually hcut)
  let ν : ℕ → ℕ := φ ∘ ψ
  have hν : StrictMono ν := hφ.comp hψ
  have hpositive : ∀ j, 0 < (d (ν j)).1 ∧ 0 < (d (ν j)).2 := by
    intro j
    have hb := hbad j
    have haxis : (d (ν j)).1 ≠ 0 := by
      intro hz
      exact hb.1 (hb.2.2.2 hz)
    have hop : 0 < (d (ν j)).2 := hb.2.2.1
    constructor <;> omega
  have hsize : Tendsto (fun j => (d (ν j)).1 + (d (ν j)).2) atTop atTop := by
    simpa only [hlen] using hν.tendsto_atTop
  have hratioν : Tendsto (fun j => ((d (ν j)).1 : ℝ) / (ν j : ℝ)) atTop (𝓝 t) := by
    simpa only [ν, ratio, Function.comp_def] using hlim.comp hψ.tendsto_atTop
  have ht01 : t ∈ Set.Icc 0 1 := ⟨htCone.1, htCone.2.trans hθ1.le⟩
  have hunit : ((q t).1 : ℝ) + ((q t).2 : ℝ) = 1 := by
    rw [Real.coe_toNNReal _ ht01.1, Real.coe_toNNReal _ (sub_nonneg.mpr ht01.2)]
    ring
  have hratioSize : Tendsto (fun j => ((d (ν j)).1 : ℝ) /
      (((d (ν j)).1 + (d (ν j)).2 : ℕ) : ℝ)) atTop (𝓝 ((q t).1 : ℝ)) := by
    simpa only [hlen, q, Real.coe_toNNReal _ ht01.1] using hratioν
  have hProfilesν := hprofiles x (q t) hunit (fun j => d (ν j)) hpositive hsize hratioSize
  let H : ℝ := sSup ((fun a : ℝ =>
    g (Real.toNNReal (t - a), Real.toNNReal (1 - t)) - h.1.1 * a) '' Set.Icc 0 t)
  let V : ℝ := sSup ((fun a : ℝ =>
    g (Real.toNNReal t, Real.toNNReal (1 - t - a)) - h.1.2 * a) '' Set.Icc 0 (1 - t))
  let RN : ℕ → ℝ := fun j => restrictedNE (processEnvironment s) (fun a b => B a b s)
    x (d (ν j)) 0 (by simpa using (hpositive j).1)
  let RE : ℕ → ℝ := fun j => restrictedNE (processEnvironment s) (fun a b => B a b s)
    x (d (ν j)) 1 (by simpa using (hpositive j).2)
  have hLimits : Tendsto (fun j => RN j / (ν j : ℝ)) atTop (𝓝 H) ∧
      Tendsto (fun j => RE j / (ν j : ℝ)) atTop (𝓝 V) := by
    simpa only [RN, RE, hlen, q, Real.coe_toNNReal _ ht01.1,
      Real.coe_toNNReal _ (sub_nonneg.mpr ht01.2)] using hProfilesν
  have hComparison := (restricted_profiles_compare_outside_contact g hHom hConc h hMajorant
    left right hLeft hRight hContact t ht01).1
      (htCone.2.trans_lt hConeSep)
  -- Strictness is the derivative/small-positive-exit conjunction, not plane equality.
  have hLosing : H = g (q t) := hComparison.1
  have hStrict : H < V := hComparison.2.2
  have hOrdinaryν := hOrdinaryLimit d hlen ν hν t hratioν
  have hRestrictedOrder := hLimits.1.eventually_lt hLimits.2 hStrict
  have hOrdinaryOrder := hOrdinaryν.eventually_lt hLimits.2
    (by rw [← hLosing]; exact hStrict)
  obtain ⟨j, hjRestricted, hjOrdinary⟩ := (hRestrictedOrder.and hOrdinaryOrder).exists
  have hnpos : 0 < ν j := (hbad j).2.1
  have hnR : 0 < (ν j : ℝ) := by exact_mod_cast hnpos
  have hClass : RN j < RE j := (div_lt_div_iff_of_pos_right hnR).mp hjRestricted
  have hOrd : lastPassage (processEnvironment s) x (d (ν j)) < RE j :=
    (div_lt_div_iff_of_pos_right hnR).mp hjOrdinary
  have hMax : max (RN j) (RE j) = B x (terminal (ν j)) s :=
    restrictedNE_max_eq_cocycle (processEnvironment s) (fun a b => B a b s) ha hr
      x (d (ν j)) (hpositive j).1 (hpositive j).2
  rw [max_eq_right hClass.le] at hMax
  have hBridge : lastPassage (field (ν j)) x (d (ν j)) ≤
      max (RN j) (lastPassage (processEnvironment s) x (d (ν j))) :=
    (one_sided_boundary_passage_le_max_restrictedNE (processEnvironment s) (fun a b => B a b s)
      x (d (ν j)) (hpositive j).1 (hpositive j).2).1
  have hGood : good (ν j) := ⟨hnpos,
    hBridge.trans_lt ((max_lt hClass hOrd).trans_eq hMax)⟩
  exact (hbad j).1 hGood

end LPP.Busemann
