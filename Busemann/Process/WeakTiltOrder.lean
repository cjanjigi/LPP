/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
-/
module

public import Busemann.Process.NativeExactSeed
public import Busemann.Finite.TiltOrder
public import Busemann.Geometry.SupportOrder
public import LPP_Foundations.Analysis.AbsoluteMomentShape
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Tactic

/-! Raw coordinate order inherited by an actual shared-horizon weak limit. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal NNReal Topology

namespace LPP.Busemann

/-- The actual weak limit of the native shared-horizon laws satisfies the raw
non-strict order constraint between every pair of supplied support tilts.
Finite-horizon order is valid at every sampled terminal level, including
inactive levels. -/
theorem finiteBusemann_raw_order_of_actual_weak_limit
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g)
    (h : ℕ → SupportTilt g)
    (P : ProbabilityMeasure ProcessSample) (φ : ℕ → ℕ)
    (hweak :
      let ν : ℕ → ProbabilityMeasure ProcessSample := fun n =>
        (show ProbabilityMeasure (Environment × Fin (n + 1)) from
          ⟨finiteBusemannSharedHorizonLaw μ n, by
            change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
            infer_instance⟩).map
          (fun p => (p.1,
            finiteBusemannArrayAtSharedHorizon n (fun j => (h j).val) p))
      Tendsto (ν ∘ φ) atTop (𝓝 P)) :
    let Q : Set ProcessSample :=
      {s | ∀ j k x, (h j).val.1 ≤ (h k).val.1 →
        (s.2 j x 0 ≥ s.2 k x 0 ∧ s.2 j x 1 ≤ s.2 k x 1)}
    IsClosed Q ∧ MeasurableSet Q ∧ (P : Measure ProcessSample) Q = 1 := by
  classical
  let Q : Set ProcessSample :=
    {s | ∀ j k x, (h j).val.1 ≤ (h k).val.1 →
      (s.2 j x 0 ≥ s.2 k x 0 ∧ s.2 j x 1 ≤ s.2 k x 1)}
  let ν : ℕ → ProbabilityMeasure ProcessSample := fun n =>
    (show ProbabilityMeasure (Environment × Fin (n + 1)) from
      ⟨finiteBusemannSharedHorizonLaw μ n, by
        change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
        infer_instance⟩).map
      (fun p => (p.1,
        finiteBusemannArrayAtSharedHorizon n (fun j => (h j).val) p))

  have hgeometry := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  have hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z := by
    intro c z
    change g (c * z.1, c * z.2) = (c : ℝ) * g z
    exact hgeometry.2.1 c z

  have hsecond (j k : ℕ) (hfirst : (h j).val.1 ≤ (h k).val.1) :
      (h k).val.2 ≤ (h j).val.2 := by
    have horder := supportTilt_coordinate_order g hhom (h j) (h k)
    rcases lt_or_eq_of_le hfirst with hlt | heq
    · exact le_of_lt (horder.1 hlt).1
    · rw [horder.2 heq]

  have heval (j : ℕ) (x : Lattice) (i : Fin 2) :
      Continuous (fun s : ProcessSample => s.2 j x i) :=
    (continuous_apply i).comp ((continuous_apply x).comp
      ((continuous_apply j).comp continuous_snd))
  have hQclosed : IsClosed Q := by
    change IsClosed {s : ProcessSample | ∀ j k (x : Lattice),
      (h j).val.1 ≤ (h k).val.1 →
      (s.2 j x 0 ≥ s.2 k x 0 ∧ s.2 j x 1 ≤ s.2 k x 1)}
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro k
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _hfirst
    exact (isClosed_le (heval k x 0) (heval j x 0)).inter
      (isClosed_le (heval j x 1) (heval k x 1))

  let S : (n : ℕ) → Environment × Fin (n + 1) → ProcessSample := fun n p =>
    (p.1, finiteBusemannArrayAtSharedHorizon n (fun j => (h j).val) p)

  have hfinite (n : ℕ) (p : Environment × Fin (n + 1)) : S n p ∈ Q := by
    change ∀ j k x, (h j).val.1 ≤ (h k).val.1 →
      (S n p).2 j x 0 ≥ (S n p).2 k x 0 ∧
        (S n p).2 j x 1 ≤ (S n p).2 k x 1
    intro j k x hfirst
    have horder := finiteBusemannEdge_order_of_tilt p.1 (h j).val (h k).val
      hfirst (hsecond j k hfirst) x ((p.2.val + 1 : ℕ) : ℤ)
    simpa only [S, finiteBusemannArrayAtSharedHorizon] using horder

  have hS (n : ℕ) : Measurable (S n) :=
    measurable_fst.prodMk (measurable_finiteBusemannArrayAtSharedHorizon n
      (fun j => (h j).val))

  have hνzero (n : ℕ) : (ν n : Measure ProcessSample) Qᶜ = 0 := by
    have hpre : S n ⁻¹' Qᶜ = ∅ := by
      ext p
      constructor
      · intro hp
        exact False.elim (hp (hfinite n p))
      · intro hp
        exact False.elim hp
    calc
      (ν n : Measure ProcessSample) Qᶜ =
          (finiteBusemannSharedHorizonLaw μ n) (S n ⁻¹' Qᶜ) := by
        rw [ProbabilityMeasure.toMeasure_map,
          Measure.map_apply (hS n) hQclosed.measurableSet.compl]
        rfl
      _ = 0 := by rw [hpre, measure_empty]

  have hweak' : Tendsto (ν ∘ φ) atTop (𝓝 P) := hweak
  have hbadzero : Tendsto (fun n => (ν (φ n) : Measure ProcessSample) Qᶜ)
      atTop (𝓝 0) := by
    simpa only [hνzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    hweak' hQclosed.isOpen_compl
  change (P : Measure ProcessSample) Qᶜ ≤
    liminf (fun n => (ν (φ n) : Measure ProcessSample) Qᶜ) atTop at hle
  have hzero : (P : Measure ProcessSample) Qᶜ = 0 := by
    apply le_antisymm
    · simpa only [hbadzero.liminf_eq] using hle
    · exact bot_le
  have hQae : ∀ᵐ s ∂(P : Measure ProcessSample), s ∈ Q := by
    rw [ae_iff]
    exact hzero
  have hQprob : (P : Measure ProcessSample) Q = 1 :=
    (mem_ae_iff_prob_eq_one hQclosed.measurableSet).mp hQae
  exact ⟨hQclosed, hQclosed.measurableSet, hQprob⟩

end LPP.Busemann
