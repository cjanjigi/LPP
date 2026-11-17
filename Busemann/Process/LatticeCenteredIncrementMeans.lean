/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.LatticeDirectionalConditionalMeans
import Mathlib.Tactic

/-! Conditional centering for a generic lattice action. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped Topology

namespace LPP.Busemann

/-- A generic full-action centered unit increment has zero conditional mean
under both the full and unit-shift invariant sigma algebras. This is the
centering step before JR arXiv:1810.03580v3, Appendix B, Lemma B.5. -/
theorem centered_increment_condExp_zero_of_action
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω)
    (hzero : ∀ s : Ω, T 0 s = s)
    (hadd : ∀ (z w : Lattice) (s : Ω), T (z + w) s = T z (T w s))
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (hInt : ∀ x y, Integrable (B x y) P) (i : Fin 2) :
    let mΩ0 : MeasurableSpace Ω := inferInstance
    let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
    let e : Lattice := finiteEdgeStep i
    let J : MeasurableSpace Ω := @MeasurableSpace.invariants Ω mΩ0 (T e)
    letI : MeasurableSpace Ω := mΩ0
    let φ : Ω → ℝ := fun s => B 0 e s - P[B 0 e | I] s
    Measurable φ ∧ Integrable φ P ∧
      P[φ | I] =ᵐ[P] (0 : Ω → ℝ) ∧
      P[φ | J] =ᵐ[P] (0 : Ω → ℝ) := by
  let mΩ0 : MeasurableSpace Ω := inferInstance
  let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
  let e : Lattice := finiteEdgeStep i
  let J : MeasurableSpace Ω := @MeasurableSpace.invariants Ω mΩ0 (T e)
  let : MeasurableSpace Ω := mΩ0
  let F : Ω → ℝ := B 0 e
  let U : Ω → ℝ := P[F | I]
  let φ : Ω → ℝ := fun s => F s - U s
  change Measurable φ ∧ Integrable φ P ∧
    P[φ | I] =ᵐ[P] (0 : Ω → ℝ) ∧
    P[φ | J] =ᵐ[P] (0 : Ω → ℝ)
  have hJ : J ≤ mΩ0 := MeasurableSpace.invariants_le (T e)
  have hIJ : I ≤ J := iInf_le (fun z : Lattice =>
    @MeasurableSpace.invariants Ω mΩ0 (T z)) e
  have hI : I ≤ mΩ0 := hIJ.trans hJ
  let : IsFiniteMeasure (P.trim hI) := inferInstance
  let : SigmaFinite (P.trim hI) := inferInstance
  let : IsFiniteMeasure (P.trim hJ) := inferInstance
  let : SigmaFinite (P.trim hJ) := inferInstance
  have hFmeas : Measurable F := by
    have hmap : Measurable (fun s : Ω => (((0 : Lattice), e), s)) :=
      measurable_const.prodMk measurable_id
    exact hB.1.comp hmap
  have hFint : Integrable F P := hInt 0 e
  have hUint : Integrable U P := integrable_condExp
  have hUmI : StronglyMeasurable[I] U := stronglyMeasurable_condExp
  have hUmJ : StronglyMeasurable[J] U := hUmI.mono hIJ
  have hφmeas : Measurable φ := hFmeas.sub (hUmI.mono hI).measurable
  have hφint : Integrable φ P := hFint.sub' hUint
  have hfixI : P[U | I] = U := condExp_of_stronglyMeasurable hI hUmI hUint
  have hfixJ : P[U | J] = U := condExp_of_stronglyMeasurable hJ hUmJ hUint
  have hzeroI : P[φ | I] =ᵐ[P] (0 : Ω → ℝ) := by
    have hsub : P[φ | I] =ᵐ[P] P[F | I] - P[U | I] := condExp_sub hFint hUint I
    filter_upwards [hsub] with s hs
    change P[φ | I] s = 0
    change P[φ | I] s = U s - P[U | I] s at hs
    rw [hfixI, sub_self] at hs
    exact hs
  have hzeroJ : P[φ | J] =ᵐ[P] (0 : Ω → ℝ) := by
    have hsub : P[φ | J] =ᵐ[P] P[F | J] - P[U | J] := condExp_sub hFint hUint J
    have hdir : P[F | J] =ᵐ[P] U :=
      directional_condExp_eq_full_action_condExp_of_action
        P T hzero hadd hShift B hB hInt i
    filter_upwards [hsub, hdir] with s hs hd
    change P[φ | J] s = 0
    change P[φ | J] s = P[F | J] s - P[U | J] s at hs
    rw [hfixJ, hd, sub_self] at hs
    exact hs
  exact ⟨hφmeas, hφint, hzeroI, hzeroJ⟩

end LPP.Busemann
