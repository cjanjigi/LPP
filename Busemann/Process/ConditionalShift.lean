/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.Shifts
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import ProbabilityBasics.Probability.ConditionalExpectationTransport

/-!
# Conditional expectation under the literal process shift

The conditional expectation given the environment projection transports under an
invariant literal process shift.
-/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- Conditional expectation given the environment is preserved by an invariant
literal process shift. This is the conditional projection step in JR
arXiv:1810.03580v3, equations (4.20)-(4.21). -/
theorem condExp_processShift (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (z : Lattice) (hP : P.map (processShift z) = P)
    (f : ProcessSample → ℝ) (hf : Integrable f P) :
    P[f ∘ processShift z | MeasurableSpace.comap processEnvironment
      (inferInstance : MeasurableSpace Environment)] =ᵐ[P]
      (P[f | MeasurableSpace.comap processEnvironment
        (inferInstance : MeasurableSpace Environment)]) ∘ processShift z := by
  let mProc : MeasurableSpace ProcessSample := inferInstance
  let e : @MeasurableEquiv ProcessSample ProcessSample mProc mProc :=
    { toEquiv :=
        { toFun := processShift z
          invFun := processShift (-z)
          left_inv := processShift_neg_processShift z
          right_inv := by
            intro s
            simpa only [neg_neg] using processShift_neg_processShift (-z) s }
      measurable_toFun := measurable_processShift z
      measurable_invFun := measurable_processShift (-z) }
  let mEnv := MeasurableSpace.comap processEnvironment
    (inferInstance : MeasurableSpace Environment)
  let : MeasurableSpace ProcessSample := mProc

  -- The environment projection sigma algebra lies below the process ambient space.
  have hm : mEnv ≤ mProc := by
    change MeasurableSpace.comap Prod.fst
      (inferInstance : MeasurableSpace Environment) ≤ mProc
    exact measurable_fst.comap_le

  -- The premise makes the local measurable equivalence measure preserving.
  have he : @MeasurePreserving ProcessSample ProcessSample mProc mProc
      (processShift z) P P :=
    ⟨measurable_processShift z, hP⟩

  -- The process shift translates the environment projection by its canonical equivalence.
  have hEnv : MeasurableSpace.comap (processShift z) mEnv = mEnv := by
    change MeasurableSpace.comap (processShift z)
      (MeasurableSpace.comap processEnvironment
        (inferInstance : MeasurableSpace Environment)) = _
    rw [MeasurableSpace.comap_comp]
    have hprojection : processEnvironment ∘ processShift z =
        environmentTranslationEquiv z ∘ processEnvironment := by
      funext s
      exact processEnvironment_processShift z s
    rw [hprojection, ← MeasurableSpace.comap_comp,
      (environmentTranslationEquiv z).measurableEmbedding.comap_eq]

  exact @ProbabilityBasics.condExp_comp_measurePreserving
    ProcessSample mProc mEnv hm P inferInstance e he hEnv f hf

end LPP.Busemann
