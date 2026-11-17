/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.RandomCocycle
public import Busemann.Process.ConditionalProjection
public import Busemann.Process.ConditionalShift
public import LPP_Foundations.Probability.TranslationEquiv

/-! Conditional projection of an integrable coupled cocycle to the environment. -/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- An integrable shift-covariant coupled cocycle has a canonical conditional
projection, retaining its pairwise means, as in JR arXiv:1810.03580v3,
proof of Theorem 4.8 after (4.20). -/
theorem exists_canonical_condExp_cocycle
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z, P.map (processShift z) = P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P) :
    let mEnv := MeasurableSpace.comap processEnvironment
      (inferInstance : MeasurableSpace Environment)
    ∃ b : Lattice → Lattice → Environment → ℝ,
      is_shift_covariant_cocycle (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω) b ∧
      (∀ x y, Integrable (b x y) (environmentLaw μ)) ∧
      (∀ x y, ∀ᵐ s ∂P, b x y (processEnvironment s) = P[B x y | mEnv] s) ∧
      (∀ x y, (∫ ω, b x y ω ∂environmentLaw μ) = ∫ s, B x y s ∂P) := by
  classical
  let mProc : MeasurableSpace ProcessSample := inferInstance
  let mEnv := MeasurableSpace.comap processEnvironment
    (inferInstance : MeasurableSpace Environment)
  let : MeasurableSpace ProcessSample := mProc
  have hscalar (x y : Lattice) :
      ∃ b : Environment → ℝ,
        Measurable b ∧
        (∀ᵐ s ∂P, b (processEnvironment s) = P[B x y | mEnv] s) ∧
        Integrable b (environmentLaw μ) ∧
        (∫ ω, b ω ∂environmentLaw μ) = ∫ s, B x y s ∂P ∧
        ∀ b' : Environment → ℝ, Measurable b' →
          (∀ᵐ s ∂P, b' (processEnvironment s) = P[B x y | mEnv] s) →
          b' =ᵐ[environmentLaw μ] b := by
    exact exists_canonical_condExp_representative μ P hMarginal (B x y) (hInt x y)
  choose b hb using hscalar
  have hbMeas (x y : Lattice) : Measurable (b x y) := (hb x y).1
  have hbRep (x y : Lattice) :
      ∀ᵐ s ∂P, b x y (processEnvironment s) = P[B x y | mEnv] s :=
    (hb x y).2.1
  have hbInt (x y : Lattice) : Integrable (b x y) (environmentLaw μ) :=
    (hb x y).2.2.1
  have hbMean (x y : Lattice) :
      (∫ ω, b x y ω ∂environmentLaw μ) = ∫ s, B x y s ∂P :=
    (hb x y).2.2.2.1
  have hbUnique (x y : Lattice) (b' : Environment → ℝ) (hb' : Measurable b')
      (hrep' : ∀ᵐ s ∂P, b' (processEnvironment s) = P[B x y | mEnv] s) :
      b' =ᵐ[environmentLaw μ] b x y :=
    (hb x y).2.2.2.2 b' hb' hrep'

  -- Conditional linearity transfers each additive identity.
  have hadd (x y z : Lattice) :
      ∀ᵐ ω ∂environmentLaw μ, b x y ω + b y z ω = b x z ω := by
    have haddB : B x y + B y z =ᵐ[P] B x z := by
      filter_upwards [hB.2.2] with s hs
      exact hs x y z
    have hceAdd : P[B x y + B y z | mEnv] =ᵐ[P]
        P[B x y | mEnv] + P[B y z | mEnv] :=
      condExp_add (hInt x y) (hInt y z) mEnv
    have hceEq : P[B x y + B y z | mEnv] =ᵐ[P] P[B x z | mEnv] :=
      condExp_congr_ae haddB
    have hrep : ∀ᵐ s ∂P,
        (fun ω => b x y ω + b y z ω) (processEnvironment s) = P[B x z | mEnv] s := by
      filter_upwards [hbRep x y, hbRep y z, hceAdd, hceEq] with s hx hy ha he
      change P[B x y + B y z | mEnv] s =
        P[B x y | mEnv] s + P[B y z | mEnv] s at ha
      exact (congrArg₂ (· + ·) hx hy).trans (ha.symm.trans he)
    exact hbUnique x z (fun ω => b x y ω + b y z ω)
      ((hbMeas x y).add (hbMeas y z)) hrep

  -- Conditional transport and projection intertwining transfer each shift.
  have hcov (x y z : Lattice) :
      ∀ᵐ ω ∂environmentLaw μ,
        b (x + z) (y + z) ω = b x y (environmentTranslationEquiv z ω) := by
    have hpres : MeasurePreserving (processShift z) P P :=
      ⟨measurable_processShift z, hShift z⟩
    have hrepShift := hpres.quasiMeasurePreserving.ae (hbRep x y)
    have hceEq : P[B (x + z) (y + z) | mEnv] =ᵐ[P]
        P[(B x y) ∘ processShift z | mEnv] :=
      condExp_congr_ae (hB.2.1 x y z)
    have hceShift := condExp_processShift P z (hShift z) (B x y) (hInt x y)
    have hrep : ∀ᵐ s ∂P,
        (fun ω => b x y (environmentTranslationEquiv z ω)) (processEnvironment s) =
          P[B (x + z) (y + z) | mEnv] s := by
      filter_upwards [hrepShift, hceEq, hceShift] with s hr he ht
      change b x y (processEnvironment (processShift z s)) =
        P[B x y | mEnv] (processShift z s) at hr
      change P[(B x y) ∘ processShift z | mEnv] s =
        P[B x y | mEnv] (processShift z s) at ht
      rw [← processEnvironment_processShift z s]
      exact hr.trans (ht.symm.trans he.symm)
    exact (hbUnique (x + z) (y + z)
      (fun ω => b x y (environmentTranslationEquiv z ω))
      ((hbMeas x y).comp (environmentTranslationEquiv z).measurable) hrep).symm

  have hJoint : Measurable (fun p : (Lattice × Lattice) × Environment =>
      b p.1.1 p.1.2 p.2) := by
    apply measurable_from_prod_countable_right
    intro p
    exact hbMeas p.1 p.2
  have hAll : ∀ᵐ ω ∂environmentLaw μ, is_additive (fun x y => b x y ω) := by
    apply ae_all_iff.2
    intro x
    apply ae_all_iff.2
    intro y
    apply ae_all_iff.2
    intro z
    exact hadd x y z
  exact ⟨b, ⟨hJoint, hcov, hAll⟩, hbInt, hbRep, hbMean⟩

end LPP.Busemann
