/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.ProcessSample
public import Busemann.Frozen.Definitions.FiniteBusemannSharedHorizonLaw
public import Busemann.Frozen.Definitions.FiniteBusemannArrayAtSharedHorizon
public import Busemann.Frozen.Definitions.SupportTilt
public import Martin2004.Shape.ExpectedRateShape
public import ProbabilityBasics.Probability.AbsoluteMomentTail
public import ProbabilityBasics.Probability.JointProductTightness
public import LPP_Foundations.Probability.EnvironmentLaw
import Busemann.Finite.SharedHorizonMoments
import Busemann.Finite.Measurability
import LPP_Foundations.Probability.MartinFirstMoment
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Nat

/-! One weak limit for the literal shared-horizon array together with its
canonical environment, following JR1810.03580v3, proof of Theorem 4.8 after
(4.17). All coordinates retain one common finite horizon and subsequence. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

/-- Native moments give one weak subsequential joint limit of the actual finite
shared-horizon laws, with exactly the canonical environment marginal. This is
the tightness step of JR1810.03580v3, proof of Theorem 4.8 after (4.17). -/
theorem exists_finiteBusemann_joint_probabilityMeasure_subseq
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) (h : ℕ → SupportTilt g) :
    let ν : ℕ → ProbabilityMeasure ProcessSample := fun n =>
      (show ProbabilityMeasure (Environment × Fin (n + 1)) from
        ⟨finiteBusemannSharedHorizonLaw μ n, by
          change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
          infer_instance⟩).map
        (fun p => (p.1, finiteBusemannArrayAtSharedHorizon n (fun j => (h j).val) p))
    ∃ P : ProbabilityMeasure ProcessSample, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (ν ∘ φ) atTop (𝓝 P) ∧
        (P : Measure ProcessSample).fst = environmentLaw μ := by
  classical
  let q (n : ℕ) : ProbabilityMeasure (Environment × Fin (n + 1)) :=
    ⟨finiteBusemannSharedHorizonLaw μ n, by
      change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
      infer_instance⟩
  let S (n : ℕ) (p : Environment × Fin (n + 1)) : ProcessSample :=
    (p.1, finiteBusemannArrayAtSharedHorizon n (fun j => (h j).val) p)
  let ν : ℕ → ProbabilityMeasure ProcessSample := fun n => (q n).map (S n)
  change ∃ P : ProbabilityMeasure ProcessSample, ∃ φ : ℕ → ℕ,
    StrictMono φ ∧ Tendsto (ν ∘ φ) atTop (𝓝 P) ∧
      (P : Measure ProcessSample).fst = environmentLaw μ
  -- Measurability ensures these total map operations are genuine pushforwards.
  have hS (n : ℕ) : Measurable (S n) :=
    measurable_fst.prodMk
      (measurable_finiteBusemannArrayAtSharedHorizon n (fun j => (h j).val))
  have hνfst (n : ℕ) : (ν n : Measure ProcessSample).fst = environmentLaw μ := by
    change ((finiteBusemannSharedHorizonLaw μ n).map
      (fun p => (p.1, finiteBusemannArrayAtSharedHorizon n (fun j => (h j).val) p))).fst = _
    rw [Measure.fst_map_prodMk measurable_fst
      (measurable_finiteBusemannArrayAtSharedHorizon n (fun j => (h j).val))]
    change (uniformOriginProduct (environmentLaw μ) n).map Prod.fst = _
    exact (uniformOriginProduct_fst (environmentLaw μ) n).map_eq

  -- Flatten and reindex every actual coordinate bijectively, with no padding.
  let A : Type := ℕ → Lattice → Fin 2 → ℝ
  let I : Type := (ℕ × Lattice) × Fin 2
  let eL : Lattice ≃ ℕ :=
    (Equiv.prodCongr Equiv.intEquivNat Equiv.intEquivNat).trans Nat.pairEquiv
  let eN : (ℕ × Lattice) ≃ ℕ :=
    (Equiv.prodCongr (Equiv.refl ℕ) eL).trans Nat.pairEquiv
  let e : I ≃ ℤ := ((Equiv.prodCongr eN (Equiv.refl (Fin 2))).trans
    (Nat.divModEquiv 2).symm).trans Equiv.intEquivNat.symm
  -- Keep the explicit bijection, but use its laws without reducing its arithmetic.
  clear_value e
  let c : (I → ℝ) ≃ₜ A :=
    (Homeomorph.piCurry (X := ℕ × Lattice) (Y := Fin 2) (Z := ℝ)).trans
      (Homeomorph.piCurry (X := ℕ) (Y := Lattice) (Z := Fin 2 → ℝ))
  let R : A ≃ₜ (ℤ → ℝ) := c.symm.trans
    (Homeomorph.piCongrLeft (Y := fun _ : ℤ => ℝ) e)
  let T : ProcessSample ≃ₜ (Environment × (ℤ → ℝ)) :=
    (Homeomorph.refl Environment).prodCongr R
  have hRat (a : A) (i : I) : R a (e i) = a i.1.1 i.1.2 i.2 := by
    calc
      R a (e i) = c.symm a i := by
        change (Homeomorph.piCongrLeft (Y := fun _ : ℤ => ℝ) e)
          (c.symm a) (e i) = c.symm a i
        exact Homeomorph.piCongrLeft_apply_apply (Y := fun _ : ℤ => ℝ)
          e (c.symm a) i
      _ = _ := rfl
  have hR (a : A) (k : ℤ) : R a k =
      a (e.symm k).1.1 (e.symm k).1.2 (e.symm k).2 := by
    simpa only [e.apply_symm_apply] using hRat a (e.symm k)
  let η : ℕ → ProbabilityMeasure (Environment × (ℤ → ℝ)) := fun n => (ν n).map T
  let ρ : ProbabilityMeasure Environment := ⟨environmentLaw μ, inferInstance⟩
  have hηfst (n : ℕ) : (η n : Measure (Environment × (ℤ → ℝ))).fst =
      (ρ : Measure Environment) := by
    change (((ν n : Measure ProcessSample).map T).map Prod.fst) = environmentLaw μ
    rw [Measure.map_map measurable_fst T.measurable]
    have hfirst : Prod.fst ∘ T = (Prod.fst : ProcessSample → Environment) := rfl
    rw [hfirst]
    exact hνfst n

  -- Produce actual finite integrability and native coordinate bounds internally.
  obtain ⟨p, hp, hpMoment⟩ := hmoment
  have hpos := (ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
    μ hp hpMoment).2
  have hneg := ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment
    μ hp hpMoment
  have hfirstMoment := integrable_id_of_martin_tails μ hneg hpos
  have hi (n : ℕ) (a : I) : Integrable
      (fun p : Environment × Fin (n + 1) => finiteBusemannEdge p.1
        (h a.1.1).val a.1.2 ((p.2.val + 1 : ℕ) : ℤ) a.2)
      (finiteBusemannSharedHorizonLaw μ n) := by
    rw [finiteBusemannSharedHorizonLaw]
    exact integrable_uniformOrigin_family (environmentLaw μ) n
      (fun k ω => finiteBusemannEdge ω (h a.1.1).val a.1.2 ((k.val + 1 : ℕ) : ℤ) a.2)
      (fun k => measurable_finiteBusemannEdge (h a.1.1).val a.1.2 ((k.val + 1 : ℕ) : ℤ) a.2)
      (fun k => integrable_finiteBusemannEdge μ hfirstMoment (h a.1.1).val a.1.2
        ((k.val + 1 : ℕ) : ℤ) a.2)
  have hchoose (a : I) : ∃ C : ℝ, ∀ n : ℕ,
      (∫ p : Environment × Fin (n + 1), |finiteBusemannEdge p.1
        (h a.1.1).val a.1.2 ((p.2.val + 1 : ℕ) : ℤ) a.2|
        ∂finiteBusemannSharedHorizonLaw μ n) ≤ C := by
    obtain ⟨C, _, hC⟩ := exists_uniform_integral_abs_finiteBusemannEdge_sharedHorizon_bound
      μ ⟨p, hp, hpMoment⟩ g hg (h a.1.1) a.1.2 a.2
    exact ⟨C, hC⟩
  choose C hC using hchoose
  have hactual (n : ℕ) (a : I) :
      (∫⁻ p : Environment × Fin (n + 1),
        ENNReal.ofReal ‖(S n p).2 a.1.1 a.1.2 a.2‖ ∂(q n : Measure _)) ≤
          ENNReal.ofReal (C a) := by
    change (∫⁻ p : Environment × Fin (n + 1), ENNReal.ofReal ‖finiteBusemannEdge p.1
      (h a.1.1).val a.1.2 ((p.2.val + 1 : ℕ) : ℤ) a.2‖
        ∂finiteBusemannSharedHorizonLaw μ n) ≤ _
    have heq := ofReal_integral_eq_lintegral_ofReal (hi n a).norm
      (ae_of_all _ (fun p => norm_nonneg (finiteBusemannEdge p.1
        (h a.1.1).val a.1.2 ((p.2.val + 1 : ℕ) : ℤ) a.2)))
    rw [← heq]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Real.norm_eq_abs] using hC a n
  have hbound (n : ℕ) (k : ℤ) :
      (∫⁻ z : Environment × (ℤ → ℝ), ENNReal.ofReal ‖z.2 k‖
        ∂(η n : Measure (Environment × (ℤ → ℝ)))) ≤ ENNReal.ofReal (C (e.symm k)) := by
    have hf : Measurable (fun z : Environment × (ℤ → ℝ) => ENNReal.ofReal ‖z.2 k‖) :=
      ENNReal.measurable_ofReal.comp
        (measurable_norm.comp ((measurable_pi_apply k).comp measurable_snd))
    change (∫⁻ z : Environment × (ℤ → ℝ), ENNReal.ofReal ‖z.2 k‖
      ∂Measure.map T ((q n : Measure _).map (S n))) ≤ _
    have hfT : Measurable (fun z : ProcessSample => ENNReal.ofReal ‖(T z).2 k‖) :=
      hf.comp T.measurable
    rw [lintegral_map hf T.measurable, lintegral_map hfT (hS n)]
    change (∫⁻ p : Environment × Fin (n + 1), ENNReal.ofReal ‖R (S n p).2 k‖
      ∂(q n : Measure _)) ≤ _
    simp_rw [hR]
    exact hactual n (e.symm k)

  -- The existing theorem selects one joint limit and one common subsequence.
  obtain ⟨κ, φ, hφ, hlim, hκfst⟩ :=
    exists_joint_probabilityMeasure_tendsto_subseq_of_coordinate_moments ρ η hηfst
      (fun k => ENNReal.ofReal (C (e.symm k)))
      (fun _ => ENNReal.ofReal_ne_top) hbound
  have hback (n : ℕ) : (η n).map T.symm = ν n := by
    apply Subtype.ext
    change ((ν n : Measure ProcessSample).map T).map T.symm = (ν n : Measure ProcessSample)
    rw [Measure.map_map T.symm.measurable T.measurable]
    have hcomp : T.symm ∘ T = id := funext T.symm_apply_apply
    rw [hcomp, Measure.map_id]
  refine ⟨κ.map T.symm, φ, hφ, ?_, ?_⟩
  · have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (η ∘ φ) κ hlim T.symm.continuous
    have heq : (fun n => ((η ∘ φ) n).map T.symm) = ν ∘ φ := by
      funext n
      exact hback (φ n)
    rw [heq] at ht
    exact ht
  · change ((κ : Measure (Environment × (ℤ → ℝ))).map T.symm).map Prod.fst = environmentLaw μ
    rw [Measure.map_map measurable_fst T.symm.measurable]
    have hfirst : Prod.fst ∘ T.symm =
        (Prod.fst : Environment × (ℤ → ℝ) → Environment) := rfl
    rw [hfirst]
    exact hκfst

end LPP.Busemann
