/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.CalibratedCoordinateEscape
public import Busemann.Process.RightmostPaths
import Busemann.Process.PathTotalCalibration
import Mathlib.Tactic

/-! Coordinate escape for the actual rightmost cocycle paths. -/

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal NNReal Topology

namespace LPP.Busemann

/-- Under the generic calibrated-coordinate escape assumptions, the actual
rightmost path from every lattice site has both coordinates tending to
infinity, on one common almost-sure event. This is the rightmost-path
specialization of GRS arXiv:1510.00860v1, Appendix A.6. -/
theorem ae_rightmostCocyclePath_tendsto_coordinates_of_action
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω) (weights : Ω → Environment)
    (hzero : ∀ ω, T 0 ω = ω)
    (hadd : ∀ z w ω, T (z + w) ω = T z (T w ω))
    (hShift : ∀ z, MeasurePreserving (T z) P P)
    (hWeightsMeas : Measurable weights)
    (hMarginal : P.map weights = environmentLaw μ)
    (hWeightsShift : ∀ z x ω, weights (T z ω) x = weights ω (z + x))
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (hRec : recovers_weight_map_ae P weights B)
    (hInt₁ : Integrable (B 0 (1, 0)) P)
    (hInt₂ : Integrable (B 0 (0, 1)) P) :
    ∀ᵐ ω ∂P, ∀ x : Lattice,
      Tendsto (fun n => (rightmostCocyclePath (fun y z => B y z ω) x n).1) atTop atTop ∧
      Tendsto (fun n => (rightmostCocyclePath (fun y z => B y z ω) x n).2) atTop atTop := by
  classical
  -- Use the existing event for every calibrated path family, then add the
  -- pointwise cocycle and recovery events before selecting any start.
  have hGeneric := ae_calibrated_endpoints_tendsto_coordinates_of_action
    μ hμ hmoment P T weights hzero hadd hShift hWeightsMeas hMarginal
    hWeightsShift B hB hRec hInt₁ hInt₂
  filter_upwards [hGeneric, hB.2.2, hRec] with ω hEscape hAdd hRecover
  intro x
  let C : Lattice → Lattice → ℝ := fun y z => B y z ω
  -- Choose actual calibrated prefixes, retaining each trace and endpoint.
  let q (n : ℕ) := Classical.choose
    (exists_rightmostCocyclePath_prefix (weights ω) C hAdd hRecover x n)
  have hq (n : ℕ) := Classical.choose_spec
    (exists_rightmostCocyclePath_prefix (weights ω) C hAdd hRecover x n)
  let d (n : ℕ) : ℕ × ℕ := ((q n).1.val, n - (q n).1.val)
  let p (n : ℕ) : LPPDifferentiability.Path x (d n) := (q n).2
  have hlen (n : ℕ) : (d n).1 + (d n).2 = n := by
    dsimp only [d]
    have h := (q n).1.isLt
    omega
  have hTerminal (n : ℕ) :
      rightmostCocyclePath C x n = x + (((d n).1 : ℤ), ((d n).2 : ℤ)) := by
    have htrace := (hq n).1 n (by have h := (q n).1.isLt; omega)
    have hidx :
        (⟨n, by have h := (q n).1.isLt; omega⟩ :
          Fin ((q n).1.val + (n - (q n).1.val) + 1)) =
          Fin.last ((q n).1.val + (n - (q n).1.val)) := by
      apply Fin.ext
      simp only [Fin.val_last]
      have h := (q n).1.isLt
      omega
    rw [hidx, (q n).2.finish] at htrace
    simpa only [d] using htrace.symm
  have hCal (n : ℕ) (k : Fin ((d n).1 + (d n).2)) :
      B ((p n).vertex k.castSucc) ((p n).vertex k.succ) ω =
        weights ω ((p n).vertex k.castSucc) := by
    have htotal : pathWeight (weights ω) (p n) =
        C x (x + (((d n).1 : ℤ), ((d n).2 : ℤ))) := by
      calc
        pathWeight (weights ω) (p n) = C x (rightmostCocyclePath C x n) :=
          (hq n).2.1
        _ = C x (x + (((d n).1 : ℤ), ((d n).2 : ℤ))) :=
          congrArg (C x) (hTerminal n)
    exact (pathWeight_eq_cocycle_iff_calibrated (weights ω) C hAdd hRecover
      x (d n) (p n)).mp htotal k
  have hCoordinates := hEscape x d hlen p hCal
  have hFirst : (fun n => x.1 + ((d n).1 : ℤ)) =
      (fun n => (rightmostCocyclePath C x n).1) := by
    funext n
    have h := congrArg Prod.fst (hTerminal n)
    simpa only [Prod.fst_add] using h.symm
  have hSecond : (fun n => x.2 + ((d n).2 : ℤ)) =
      (fun n => (rightmostCocyclePath C x n).2) := by
    funext n
    have h := congrArg Prod.snd (hTerminal n)
    simpa only [Prod.snd_add] using h.symm
  rw [hFirst, hSecond] at hCoordinates
  exact hCoordinates

end LPP.Busemann
