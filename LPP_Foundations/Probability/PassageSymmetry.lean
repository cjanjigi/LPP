/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Swap
public import LPP_Foundations.Probability.EnvironmentSwap
public import LPP_Foundations.Probability.PassageIntegrable
public import LPP_Foundations.Probability.PassageMeasurable
public import Mathlib.Probability.IdentDistrib

/-!
# Coordinate symmetry of finite passage laws

The actual pathwise transposition identity and invariance of the full iid
environment law give equal laws for every finite family of passage values,
and for the family indexed by all starts and displacements. Under an integrable
marginal, these are integrable real passage values and their expectations agree.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- Any indexed family of finite passage values is measurable in the environment. -/
theorem measurable_lastPassage_family {ι : Type*} (u : ι → Lattice)
    (d : ι → ℕ × ℕ) :
    Measurable (fun ω : Environment => fun i : ι => lastPassage ω (u i) (d i)) :=
  Measurable.of_eval fun i => measurable_lastPassage (u i) (d i)

/-- Swapping both endpoints leaves the joint law of any indexed family of
finite passage values unchanged under the full iid environment law. In
particular, this gives every finite joint passage law and the law of the whole
family indexed by all starts and displacements. -/
theorem identDistrib_lastPassage_family_swap (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {ι : Type*} (u : ι → Lattice)
    (d : ι → ℕ × ℕ) :
    IdentDistrib
      (fun ω : Environment => fun i : ι =>
        lastPassage ω (u i).swap (d i).swap)
      (fun ω : Environment => fun i : ι => lastPassage ω (u i) (d i))
      (environmentLaw μ) (environmentLaw μ) := by
  have hf := measurable_lastPassage_family u d
  have hg : Measurable (fun ω : Environment => fun i : ι =>
      lastPassage ω (u i).swap (d i).swap) :=
    Measurable.of_eval fun i => measurable_lastPassage (u i).swap (d i).swap
  have hcomp :
      (fun ω : Environment => fun i : ι =>
        lastPassage ω (u i).swap (d i).swap) =
      (fun ω : Environment => fun i : ι =>
        lastPassage (environmentSwap ω) (u i) (d i)) := by
    funext ω i
    have hEnv : environmentSwap ω = (fun z => ω z.swap) := by
      funext z
      exact environmentSwap_apply ω z
    rw [hEnv]
    exact lastPassage_swap ω (u i) (d i)
  refine ⟨hg.aemeasurable, hf.aemeasurable, ?_⟩
  calc
    (environmentLaw μ).map
        (fun ω : Environment => fun i : ι =>
          lastPassage ω (u i).swap (d i).swap) =
        (environmentLaw μ).map
          (fun ω : Environment => fun i : ι =>
            lastPassage (environmentSwap ω) (u i) (d i)) := by
      rw [hcomp]
    _ = ((environmentLaw μ).map environmentSwap).map
          (fun ω : Environment => fun i : ι => lastPassage ω (u i) (d i)) := by
      simpa only [Function.comp_def] using
        (Measure.map_map hf measurable_environmentSwap).symm
    _ = (environmentLaw μ).map
          (fun ω : Environment => fun i : ι => lastPassage ω (u i) (d i)) := by
      rw [environmentLaw_map_environmentSwap μ]

/-- The simultaneous law of passage values at every lattice start and natural
displacement is invariant under swapping both coordinates. -/
theorem identDistrib_all_lastPassage_swap (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    IdentDistrib
      (fun ω : Environment => fun e : Lattice × (ℕ × ℕ) =>
        lastPassage ω e.1.swap e.2.swap)
      (fun ω : Environment => fun e : Lattice × (ℕ × ℕ) =>
        lastPassage ω e.1 e.2)
      (environmentLaw μ) (environmentLaw μ) :=
  identDistrib_lastPassage_family_swap μ Prod.fst Prod.snd

/-- The whole-family passage map laws before and after coordinate swapping. -/
theorem environmentLaw_map_all_lastPassage_swap (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    (environmentLaw μ).map
        (fun ω : Environment => fun e : Lattice × (ℕ × ℕ) =>
          lastPassage ω e.1.swap e.2.swap) =
      (environmentLaw μ).map
        (fun ω : Environment => fun e : Lattice × (ℕ × ℕ) =>
          lastPassage ω e.1 e.2) :=
  (identDistrib_all_lastPassage_swap μ).map_eq

/-- Swapping the start and displacement preserves the law of one finite
passage value. -/
theorem identDistrib_lastPassage_swap (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (u : Lattice) (d : ℕ × ℕ) :
    IdentDistrib
      (fun ω : Environment => lastPassage ω u.swap d.swap)
      (fun ω : Environment => lastPassage ω u d)
      (environmentLaw μ) (environmentLaw μ) := by
  have h := identDistrib_lastPassage_family_swap μ
      (fun _ : Unit => u) (fun _ : Unit => d)
  convert h.comp (measurable_pi_apply ()) using 1 <;> rfl

/-- The finite passage map laws before and after coordinate swapping. -/
theorem environmentLaw_map_lastPassage_swap (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (u : Lattice) (d : ℕ × ℕ) :
    (environmentLaw μ).map (fun ω : Environment => lastPassage ω u.swap d.swap) =
      (environmentLaw μ).map (fun ω : Environment => lastPassage ω u d) :=
  (identDistrib_lastPassage_swap μ u d).map_eq

/-- Under a genuine first moment, the two finite passage variables are
integrable and their real expectations agree. No sign condition is used. -/
theorem integrable_and_integral_lastPassage_swap (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : Integrable (fun x : ℝ => x) μ)
    (u : Lattice) (d : ℕ × ℕ) :
    Integrable (fun ω : Environment => lastPassage ω u.swap d.swap)
        (environmentLaw μ) ∧
      Integrable (fun ω : Environment => lastPassage ω u d)
        (environmentLaw μ) ∧
      (∫ ω : Environment, lastPassage ω u.swap d.swap ∂environmentLaw μ) =
        ∫ ω : Environment, lastPassage ω u d ∂environmentLaw μ := by
  refine ⟨integrable_lastPassage μ hμ u.swap d.swap,
    integrable_lastPassage μ hμ u d, ?_⟩
  exact (identDistrib_lastPassage_swap μ u d).integral_eq

end LPPDifferentiability
