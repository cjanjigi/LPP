/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.GeneralizedBusemann
public import Busemann.Frozen.Definitions.ProcessEnvironment
public import Busemann.Frozen.Definitions.ProcessShift
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Busemann.Geometry.GeodesicMeasurability
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Busemann.Process.RightmostPathMeasurability
import Busemann.Process.RightmostPathGeodesic
import Lean.Elab.Tactic.Omega

/-! Conditional law of the actual rightmost cocycle path over the physical environment. -/

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability
open scoped ENNReal MeasureTheory ProbabilityTheory
namespace LPP.Busemann

private theorem locally_rightmost_le_east
    (ω : LPPDifferentiability.Environment) (u : Lattice) (γ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ) :
    pathSoutheastLE γ (fun n : ℕ => u + ((n : ℤ), (0 : ℤ))) := by
  have hbound (n : ℕ) : (γ n).1 ≤ u.1 + (n : ℤ) ∧ u.2 ≤ (γ n).2 := by
    induction n with
    | zero => simp [hγ.1]
    | succ n ih =>
        rcases hγ.2.1 n with h | h <;> rw [h] <;>
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add, Nat.cast_one] <;> omega
  intro m n hm
  have hroot := hγ.1
  simp only [hroot, Prod.fst_add, Prod.snd_add, Nat.cast_zero, add_zero] at hm
  have hmn : m = n := by omega
  subst n
  simpa only [Prod.fst_add, Prod.snd_add, add_zero] using hbound m

/-- The actual conditional rightmost-path law has genuine geodesic-fibre
support and jointly measurable inclusive CDF thresholds. Strong Existence,
source lines 754–760, before selecting a quantile. -/
theorem conditional_rightmost_path_law_and_thresholds
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B) :
    let κ : Lattice → Kernel LPPDifferentiability.Environment (ℕ → Lattice) :=
      fun u => condDistrib
        (fun s : ProcessSample => rightmostCocyclePath (fun x y => B x y s) u)
        processEnvironment P
    (∀ u : Lattice, IsMarkovKernel (κ u)) ∧
    (∀ u : Lattice,
      (environmentLaw μ) ⊗ₘ (κ u) =
        P.map (fun s : ProcessSample =>
          (processEnvironment s, rightmostCocyclePath (fun x y => B x y s) u))) ∧
    (∀ u : Lattice, Measurable
      (fun q : LPPDifferentiability.Environment × (ℕ → Lattice) =>
        (κ u) q.1 {γ : ℕ → Lattice | pathSoutheastLE γ q.2})) ∧
    (∀ u : Lattice, MeasurableSet
      {q : LPPDifferentiability.Environment ×
          ((ℕ → Lattice) × {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1}) |
        ENNReal.ofReal (q.2.2 : ℝ) ≤
          (κ u) q.1 {γ : ℕ → Lattice | pathSoutheastLE γ q.2.1}}) ∧
    ∃ A : Set LPPDifferentiability.Environment,
      MeasurableSet A ∧ environmentLaw μ A = 1 ∧
      ∀ ω ∈ A, ∀ u : Lattice,
        (κ u) ω {γ : ℕ → Lattice | IsLocallyRightmostGeodesic ω u γ} = 1 ∧
        (κ u) ω {γ : ℕ → Lattice |
          pathSoutheastLE γ (fun n : ℕ => u + ((n : ℤ), (0 : ℤ)))} = 1 := by
  classical
  let κ : Lattice → Kernel LPPDifferentiability.Environment (ℕ → Lattice) :=
    fun u => condDistrib
      (fun s : ProcessSample => rightmostCocyclePath (fun x y => B x y s) u)
      processEnvironment P
  change (∀ u : Lattice, IsMarkovKernel (κ u)) ∧
    (∀ u : Lattice,
      (environmentLaw μ) ⊗ₘ (κ u) =
        P.map (fun s : ProcessSample =>
          (processEnvironment s, rightmostCocyclePath (fun x y => B x y s) u))) ∧
    (∀ u : Lattice, Measurable
      (fun q : LPPDifferentiability.Environment × (ℕ → Lattice) =>
        (κ u) q.1 {γ : ℕ → Lattice | pathSoutheastLE γ q.2})) ∧
    (∀ u : Lattice, MeasurableSet
      {q : LPPDifferentiability.Environment ×
          ((ℕ → Lattice) × {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1}) |
        ENNReal.ofReal (q.2.2 : ℝ) ≤
          (κ u) q.1 {γ : ℕ → Lattice | pathSoutheastLE γ q.2.1}}) ∧
    ∃ A : Set LPPDifferentiability.Environment,
      MeasurableSet A ∧ environmentLaw μ A = 1 ∧
      ∀ ω ∈ A, ∀ u : Lattice,
        (κ u) ω {γ : ℕ → Lattice | IsLocallyRightmostGeodesic ω u γ} = 1 ∧
        (κ u) ω {γ : ℕ → Lattice |
          pathSoutheastLE γ (fun n : ℕ => u + ((n : ℤ), (0 : ℤ)))} = 1
  have hBMeas (x y : Lattice) : Measurable (B x y) := by
    have hArg : Measurable (fun s : ProcessSample => ((x, y), s)) :=
      measurable_const.prodMk measurable_id
    exact hB.1.1.comp hArg
  let ray (u : Lattice) (s : ProcessSample) : ℕ → Lattice :=
    rightmostCocyclePath (fun x y => B x y s) u
  have hRay (u : Lattice) : Measurable (ray u) := by
    apply measurable_pi_iff.mpr
    intro n
    exact measurable_rightmostCocyclePath B hBMeas u n
  have hJoint (u : Lattice) :
      (environmentLaw μ) ⊗ₘ (κ u) =
        P.map (fun s : ProcessSample =>
          (processEnvironment s, rightmostCocyclePath (fun x y => B x y s) u)) := by
    rw [← hMarginal]
    exact compProd_map_condDistrib measurable_fst.aemeasurable (hRay u).aemeasurable
  -- The order CDF is measurable jointly in the physical environment and barrier path.
  have hCDF (u : Lattice) : Measurable
      (fun q : LPPDifferentiability.Environment × (ℕ → Lattice) =>
        (κ u) q.1 {γ : ℕ → Lattice | pathSoutheastLE γ q.2}) := by
    let η : Kernel (LPPDifferentiability.Environment × (ℕ → Lattice)) (ℕ → Lattice) :=
      Kernel.comap (κ u) (fun q => q.1) measurable_fst
    have hRelation : MeasurableSet
        {p : (LPPDifferentiability.Environment × (ℕ → Lattice)) × (ℕ → Lattice) |
          pathSoutheastLE p.2 p.1.2} :=
      measurableSet_pathSoutheastLE.preimage (measurable_snd.prodMk measurable_fst.snd)
    have h := Kernel.measurable_kernel_prodMk_left (κ := η) hRelation
    simp only [η, Kernel.comap_apply] at h
    convert h using 1
    funext q
    congr 1
  have hThreshold (u : Lattice) : MeasurableSet
      {q : LPPDifferentiability.Environment ×
          ((ℕ → Lattice) × {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1}) |
        ENNReal.ofReal (q.2.2 : ℝ) ≤
          (κ u) q.1 {γ : ℕ → Lattice | pathSoutheastLE γ q.2.1}} := by
    have hLevel : Measurable
        (fun q : LPPDifferentiability.Environment ×
            ((ℕ → Lattice) × {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1}) =>
          ENNReal.ofReal (q.2.2 : ℝ)) :=
      ENNReal.measurable_ofReal.comp (measurable_subtype_coe.comp measurable_snd.snd)
    have hMass : Measurable
        (fun q : LPPDifferentiability.Environment ×
            ((ℕ → Lattice) × {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1}) =>
          (κ u) q.1 {γ : ℕ → Lattice | pathSoutheastLE γ q.2.1}) :=
      (hCDF u).comp (measurable_fst.prodMk measurable_snd.fst)
    exact measurableSet_le hLevel hMass
  -- The actual joint law is concentrated on locally rightmost geodesics.
  have hGraph (u : Lattice) : MeasurableSet
      {q : LPPDifferentiability.Environment × (ℕ → Lattice) |
        IsLocallyRightmostGeodesic q.1 u q.2} :=
    measurableSet_isLocallyRightmostGeodesic.preimage
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hActual (u : Lattice) : ∀ᵐ s ∂P,
      IsLocallyRightmostGeodesic (processEnvironment s) u (ray u s) := by
    filter_upwards [hB.1.2.2, hB.2.1] with s hadd hrec
    exact isLocallyRightmostGeodesic_rightmostCocyclePath
      (processEnvironment s) (fun x y => B x y s) hadd hrec u
  have hFibre (u : Lattice) : ∀ᵐ ω ∂environmentLaw μ,
      ∀ᵐ γ ∂κ u ω, IsLocallyRightmostGeodesic ω u γ := by
    have hPairAe : ∀ᵐ q ∂environmentLaw μ ⊗ₘ κ u,
        IsLocallyRightmostGeodesic q.1 u q.2 := by
      rw [hJoint u]
      have hPair : Measurable (fun s : ProcessSample => (processEnvironment s, ray u s)) :=
        measurable_fst.prodMk (hRay u)
      exact (ae_map_iff hPair.aemeasurable (hGraph u)).2 (hActual u)
    exact Measure.ae_ae_of_ae_compProd hPairAe
  have hLocalMass (u : Lattice) : Measurable
      (fun ω : LPPDifferentiability.Environment =>
        (κ u) ω {γ : ℕ → Lattice | IsLocallyRightmostGeodesic ω u γ}) := by
    have h := Kernel.measurable_kernel_prodMk_left (κ := κ u) (hGraph u)
    convert h using 1
    funext ω
    congr 1
  have hLocalOne (u : Lattice) : ∀ᵐ ω ∂environmentLaw μ,
      (κ u) ω {γ : ℕ → Lattice | IsLocallyRightmostGeodesic ω u γ} = 1 := by
    filter_upwards [hFibre u] with ω hω
    exact (mem_ae_iff_prob_eq_one (measurable_prodMk_left (hGraph u))).mp hω
  have hEastOne (u : Lattice) : ∀ᵐ ω ∂environmentLaw μ,
      (κ u) ω {γ : ℕ → Lattice |
        pathSoutheastLE γ (fun n : ℕ => u + ((n : ℤ), (0 : ℤ)))} = 1 := by
    filter_upwards [hLocalOne u] with ω hω
    have hSubset :
        {γ : ℕ → Lattice | IsLocallyRightmostGeodesic ω u γ} ⊆
          {γ : ℕ → Lattice |
            pathSoutheastLE γ (fun n : ℕ => u + ((n : ℤ), (0 : ℤ)))} := by
      intro γ hγ
      exact locally_rightmost_le_east ω u γ hγ
    have hUpper : (κ u) ω {γ : ℕ → Lattice |
        pathSoutheastLE γ (fun n : ℕ => u + ((n : ℤ), (0 : ℤ)))} ≤ 1 := by
      calc
        (κ u) ω {γ : ℕ → Lattice |
          pathSoutheastLE γ (fun n : ℕ => u + ((n : ℤ), (0 : ℤ)))} ≤
            (κ u) ω Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    exact le_antisymm hUpper (by rw [← hω]; exact measure_mono hSubset)
  have hEastMass (u : Lattice) : Measurable
      (fun ω : LPPDifferentiability.Environment =>
        (κ u) ω {γ : ℕ → Lattice |
          pathSoutheastLE γ (fun n : ℕ => u + ((n : ℤ), (0 : ℤ)))}) :=
    (hCDF u).comp (measurable_id.prodMk measurable_const)
  let A : Set LPPDifferentiability.Environment :=
    {ω | ∀ u : Lattice,
      (κ u) ω {γ : ℕ → Lattice | IsLocallyRightmostGeodesic ω u γ} = 1 ∧
      (κ u) ω {γ : ℕ → Lattice |
        pathSoutheastLE γ (fun n : ℕ => u + ((n : ℤ), (0 : ℤ)))} = 1}
  have hA : MeasurableSet A := by
    change MeasurableSet {ω : LPPDifferentiability.Environment | ∀ u : Lattice, _}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun u =>
      (measurableSet_eq_fun (hLocalMass u) measurable_const).inter
        (measurableSet_eq_fun (hEastMass u) measurable_const)
  have hAFull : environmentLaw μ A = 1 := by
    apply (mem_ae_iff_prob_eq_one hA).mp
    exact ae_all_iff.mpr fun u => (hLocalOne u).and (hEastOne u)
  exact ⟨fun _ => inferInstance, hJoint, hCDF, hThreshold,
    A, hA, hAFull, fun ω hω u => hω u⟩

end LPP.Busemann
