/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.LatticeCocycleTriangleShape
public import Martin2004.Shape.ExpectedRateShape
import Martin2004.Shape.ExpectedRateUniform
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import ProbabilityBasics.Probability.AbsoluteMomentTail
import LPP_Foundations.Model.RecoveryAntidiagonal
import LPP_Foundations.Analysis.LatticeMajorant
import Mathlib.Tactic

/-! Recovering cocycle shape for a lattice action. -/
@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped BigOperators ENNReal NNReal Topology
namespace LPP.Busemann

/-- The canonical conditional drift majorizes the expected-rate shape on the full quadrant. This is the majorant step in JR arXiv:1810.03580v3, Lemma 4.5. -/
theorem ae_canonical_drift_majorizes_expected_shape_of_action
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω) (weights : Ω → Environment) (hWeightsMeas : Measurable weights)
    (hMarginal : P.map weights = environmentLaw μ)
    (hzero : ∀ ω, T 0 ω = ω) (hadd : ∀ z w ω, T (z + w) ω = T z (T w ω))
    (hShift : ∀ z, MeasurePreserving (T z) P P)
    (B : Lattice → Lattice → Ω → ℝ) (hB : is_shift_covariant_cocycle P T B)
    (hInt : ∀ x y, Integrable (B x y) P) (hRec : recovers_weight_map_ae P weights B)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) :
    let mΩ0 : MeasurableSpace Ω := inferInstance
    let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
    letI : MeasurableSpace Ω := mΩ0
    let u : Fin 2 → Ω → ℝ := fun i => P[B 0 (finiteEdgeStep i) | I]
    ∀ᵐ ω ∂P, ∀ z : Quadrant,
      g z ≤ u 0 ω * (z.1 : ℝ) + u 1 ω * (z.2 : ℝ) := by
  classical
  let mΩ0 : MeasurableSpace Ω := inferInstance
  let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
  let : MeasurableSpace Ω := mΩ0
  let u : Fin 2 → Ω → ℝ := fun i => P[B 0 (finiteEdgeStep i) | I]
  let Δ : ℕ → Finset Lattice := fun n => insert 0
    (((Finset.Icc (0 : ℤ) (n : ℤ)).product
      (Finset.Icc (0 : ℤ) (n : ℤ))).filter
        (fun x => x.1 + x.2 ≤ (n : ℤ)))
  change ∀ᵐ s ∂P, ∀ z : Quadrant,
    g z ≤ u 0 s * (z.1 : ℝ) + u 1 s * (z.2 : ℝ)
  -- The original moment produces both tails and the actual uniform shape event.
  obtain ⟨p, hp, hpMoment⟩ := hmoment
  have hpos := (ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
    μ hp hpMoment).2
  have hneg := ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment
    μ hp hpMoment
  obtain ⟨hcont, hhom, hshape⟩ := ae_uniform_of_isExpectedRateShape μ hneg hpos hg
  have hhomScalar (c : ℝ≥0) (z : Quadrant) : g (c • z) = (c : ℝ) * g z := by
    exact hhom c z
  have hEnv : MeasurePreserving weights P (environmentLaw μ) :=
    ⟨hWeightsMeas, hMarginal⟩
  have hProcessShape := hEnv.quasiMeasurePreserving.ae hshape
  -- Use the one origin triangle producer with the same literal canonical means.
  have hTriangle := ae_uniform_recovering_cocycle_triangle_shape_of_action
    μ ⟨p, hp, hpMoment⟩ P T weights hWeightsMeas hMarginal hzero hadd hShift B hB hInt hRec
  change ∀ᵐ s ∂P, Tendsto (fun n : ℕ =>
    (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
      (fun x => |B 0 x s -
        (u 0 s * (x.1 : ℝ) + u 1 s * (x.2 : ℝ))|) / (n : ℝ))
      atTop (𝓝 0) at hTriangle
  filter_upwards [hProcessShape, hTriangle, hB.2.2, hRec] with s hs ht ha hr
  -- Actual recovery dominates the terminal-excluded passage for every natural d.
  have hdom (d : ℕ × ℕ) : lastPassage (weights s) 0 d ≤
      B 0 ((d.1 : ℤ), (d.2 : ℤ)) s := by
    have hd := (LPP.lastPassage_antidiagonal_comparison_and_attainment
      (weights s) (fun x y => B x y s) ha hr 0 (d.1 + d.2)).1 d rfl
    simpa only [zero_add] using hd
  -- Convert the actual finite supremum limit into the bridge's uniform lattice bound.
  have hcenter : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ d : ℕ × ℕ,
      N ≤ d.1 + d.2 →
      |B 0 ((d.1 : ℤ), (d.2 : ℤ)) s -
        (u 0 s * (d.1 : ℝ) + u 1 s * (d.2 : ℝ))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ) := by
    intro ε hε
    have hsmall := ht.eventually (gt_mem_nhds hε)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨max 1 N, ?_⟩
    intro d hd
    have hn1 : 1 ≤ d.1 + d.2 := (le_max_left 1 N).trans hd
    have hnN : N ≤ d.1 + d.2 := (le_max_right 1 N).trans hd
    have hnpos : (0 : ℝ) < ((d.1 + d.2 : ℕ) : ℝ) := by exact_mod_cast hn1
    have hmem : ((d.1 : ℤ), (d.2 : ℤ)) ∈ Δ (d.1 + d.2) := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · apply Finset.mem_Icc.mpr
          constructor <;> omega
        · apply Finset.mem_Icc.mpr
          constructor <;> omega
      · dsimp
        omega
    have hpoint := Finset.le_sup'
      (fun x : Lattice => |B 0 x s -
        (u 0 s * (x.1 : ℝ) + u 1 s * (x.2 : ℝ))|) hmem
    have hmax := (div_lt_iff₀ hnpos).mp (hN (d.1 + d.2) hnN)
    have hbound := hpoint.trans hmax.le
    simpa only [Int.cast_natCast] using hbound
  -- All conditional floor-bridge inputs have now been produced internally.
  exact LPP.quadrant_majorant_of_uniform_lattice_bounds g hcont hhomScalar
    (fun d => lastPassage (weights s) 0 d)
    (fun d => B 0 ((d.1 : ℤ), (d.2 : ℤ)) s)
    (u 0 s) (u 1 s) hdom hs hcenter

end LPP.Busemann
